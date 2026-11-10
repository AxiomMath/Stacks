module

public import Mathlib.Data.Finset.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic

/-!
# Divided power polynomial algebras on a set of variables

A divided power polynomial algebra `A⟨x_w : w ∈ W⟩` on an arbitrary index type is built from its
finite-variable pieces. Two things are recorded here. First, for `s ≤ t` the algebra in `s`
variables includes canonically into the one in `t` variables, preserving every divided power
monomial in an existing variable. Second, the algebra on all of `W` is the filtered colimit of
the algebras on the finite subsets `E ⊆ W`: the finite-stage maps form a cocone, and a family of
algebra maps out of the finite stages that is compatible with the transition maps descends
uniquely to the whole algebra.

Given an ideal `I` of `A`, the distinguished ideal of `A⟨x_w : w ∈ W⟩` is
`dividedPowerPolynomialIdeal I W`, the sum of the extension of `I` and the kernel of the
augmentation to `A`; it was defined for an arbitrary index type in the finite-variable
development and is reused here.

## Main definitions

* `DividedPowers.finiteVariableInclusion` — the canonical map from the divided power polynomial
  algebra in `s` variables to the one in `t` variables, for `s ≤ t`.
* `DividedPowers.setIndexedDividedPowerPolynomialAlgebra` — the divided power polynomial algebra
  with one variable for each element of an index type.
* `DividedPowers.finiteStageMap` — the transition map attached to an inclusion `E ⊆ F` of finite
  subsets of the index type.
* `DividedPowers.finiteStageInclusion` — the canonical map from the finite stage indexed by `E`
  into the set-indexed algebra.
* `DividedPowers.restrictToStage` — the restriction of a finitely supported family of
  coefficients to a finite subset of the index type containing its support.

## Main results

* `DividedPowers.stageEmbedding_restrict` — restricting to a stage containing the support is a
  section of the corresponding stage embedding.

* `DividedPowers.finiteVariableInclusion_variableMonomial` — the inclusion of finite-variable
  algebras preserves each divided power monomial in an existing variable.
* `DividedPowers.finiteStageMap_dp`, `DividedPowers.finiteStageInclusion_dp` — the finite-stage
  maps preserve divided power monomials in every variable.
* `DividedPowers.finiteStageMap_comp`, `DividedPowers.finiteStageInclusion_comp` — the transition
  maps compose along inclusions, and the finite-stage maps form a cocone over them.
* `DividedPowers.finiteStageInclusion_existsUnique_lift` — the set-indexed algebra is the
  filtered colimit of its finite stages.

## Implementation notes

Mathlib's divided power algebra on the free `A`-module `W →₀ A` is the concrete realization of
the filtered colimit over finite subsets of `W`; the finite-stage maps and their universal
property are what pin that realization down, so no separate colimit object is introduced. The
finite-variable statement is given for `s ≤ t` rather than `s < t`, which is the generality the
transition maps are used in.

The lift out of the colimit is produced by `DividedPowerAlgebra.lift'` applied to the function
sending `(n, x)` to the image of `x^[n]` under the finite-stage map for the support of `x`;
`restrictToStage` is the restriction of a finitely supported family to a finite set containing
its support, and `stageEmbedding_restrict` and `restrict_transition` say that this restriction is
a section of the stage embeddings and is compatible with the transition maps.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

namespace DividedPowers

universe u w

/-- The canonical inclusion from the divided power polynomial algebra in `s` variables to
the one in `t` variables. -/
@[stacks 07H6 "finite_variable_inclusion"]
public noncomputable def finiteVariableInclusion (A : Type u) [CommRing A]
    {s t : ℕ} (h : s ≤ t) :
    DividedPowerAlgebra A (Fin s →₀ A) →ₐ[A] DividedPowerAlgebra A (Fin t →₀ A) :=
  DividedPowerAlgebra.map A (Finsupp.lmapDomain A A (Fin.castLE h))

/-- The inclusion preserves each divided power monomial in an existing variable. -/
@[stacks 07H6 "finite_variable_inclusion"]
public theorem finiteVariableInclusion_variableMonomial (A : Type u) [CommRing A]
    {s t : ℕ} (h : s ≤ t) (i : Fin s) (n : ℕ) :
    finiteVariableInclusion A h (dividedPowerPolynomialVariableMonomial A i n) =
      dividedPowerPolynomialVariableMonomial A (Fin.castLE h i) n := by
  simp [finiteVariableInclusion, dividedPowerPolynomialVariableMonomial]

/-- The divided power polynomial algebra with one variable for each element of `W`. -/
@[stacks 07H6 "set_indexed_divided_power_polynomial_algebra"]
public abbrev setIndexedDividedPowerPolynomialAlgebra
    (A : Type u) [CommRing A] (W : Type w) :=
  DividedPowerAlgebra A (W →₀ A)

/-- The transition map between the finite-variable divided power polynomial algebras. -/
@[stacks 07H6 "set_indexed_divided_power_polynomial_algebra"]
public noncomputable def finiteStageMap (A : Type u) [CommRing A] {W : Type w}
    {E F : Finset W} (h : E ⊆ F) :
    DividedPowerAlgebra A (E →₀ A) →ₐ[A] DividedPowerAlgebra A (F →₀ A) :=
  DividedPowerAlgebra.map A (Finsupp.lmapDomain A A
    (fun e : E => (⟨e.1, h e.2⟩ : F)))

/-- The canonical map from a finite-variable algebra into the set-indexed algebra. -/
@[stacks 07H6 "set_indexed_divided_power_polynomial_algebra"]
public noncomputable def finiteStageInclusion (A : Type u) [CommRing A] {W : Type w}
    (E : Finset W) :
    DividedPowerAlgebra A (E →₀ A) →ₐ[A]
      setIndexedDividedPowerPolynomialAlgebra A W :=
  DividedPowerAlgebra.map A (Finsupp.lmapDomain A A (fun e : E => e.1))

/-- A transition map preserves divided power monomials in every variable. -/
public theorem finiteStageMap_dp (A : Type u) [CommRing A] {W : Type w}
    {E F : Finset W} (h : E ⊆ F) (e : E) (n : ℕ) :
    finiteStageMap A h (dividedPowerPolynomialVariableMonomial A e n) =
      dividedPowerPolynomialVariableMonomial A (⟨e.1, h e.2⟩ : F) n := by
  simp [finiteStageMap, dividedPowerPolynomialVariableMonomial]

/-- A finite-stage inclusion preserves divided power monomials in every variable. -/
public theorem finiteStageInclusion_dp (A : Type u) [CommRing A] {W : Type w}
    (E : Finset W) (e : E) (n : ℕ) :
    finiteStageInclusion A E (dividedPowerPolynomialVariableMonomial A e n) =
      dividedPowerPolynomialVariableMonomial A (e.1 : W) n := by
  simp [finiteStageInclusion, dividedPowerPolynomialVariableMonomial]

/-- Induced maps of divided power algebras on free modules compose like the index maps. -/
private theorem map_lmapDomain_comp (A : Type u) [CommRing A] {α β γ : Type w}
    (f : α → β) (g : β → γ) :
    (DividedPowerAlgebra.map A (Finsupp.lmapDomain A A g)).comp
      (DividedPowerAlgebra.map A (Finsupp.lmapDomain A A f)) =
      DividedPowerAlgebra.map A (Finsupp.lmapDomain A A (g ∘ f)) := by
  rw [← DividedPowerAlgebra.map_comp, Finsupp.lmapDomain_comp]

/-- The transition maps compose along inclusions of finite subsets. -/
public theorem finiteStageMap_comp (A : Type u) [CommRing A] {W : Type w}
    {E F G : Finset W} (hEF : E ⊆ F) (hFG : F ⊆ G) :
    (finiteStageMap A hFG).comp (finiteStageMap A hEF) =
      finiteStageMap A (Set.Subset.trans hEF hFG) := by
  exact map_lmapDomain_comp A _ _

/-- The canonical maps are compatible with finite-stage transitions. -/
public theorem finiteStageInclusion_comp (A : Type u) [CommRing A] {W : Type w}
    {E F : Finset W} (h : E ⊆ F) :
    (finiteStageInclusion A F).comp (finiteStageMap A h) =
      finiteStageInclusion A E := by
  exact map_lmapDomain_comp A _ _

/-- The restriction of a finitely supported family to a finite set containing its support. -/
public noncomputable def restrictToStage {A : Type u} [CommRing A] {W : Type w}
    (E : Finset W) (x : W →₀ A) (_hx : x.support ⊆ E) : E →₀ A :=
  x.comapDomain Subtype.val Subtype.val_injective.injOn

/-- Restricting to a stage containing the support is a section of the stage embedding. -/
public theorem stageEmbedding_restrict {A : Type u} [CommRing A] {W : Type w}
    (E : Finset W) (x : W →₀ A) (hx : x.support ⊆ E) :
    Finsupp.lmapDomain A A (fun e : E => e.1) (restrictToStage E x hx) = x := by
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_comapDomain (f := Subtype.val) Subtype.val_injective x
    fun y hy => ⟨⟨y, hx hy⟩, rfl⟩

/-- Restriction to a stage is compatible with the transition maps. -/
private theorem restrict_transition {A : Type u} [CommRing A] {W : Type w}
    {E F : Finset W} (hEF : E ⊆ F) (x : W →₀ A) (hx : x.support ⊆ E) :
    Finsupp.lmapDomain A A (fun e : E => (⟨e.1, hEF e.2⟩ : F))
      (restrictToStage E x hx) = restrictToStage F x (hx.trans hEF) := by
  apply Finsupp.mapDomain_injective (f := Subtype.val) Subtype.val_injective
  change ((Finsupp.lmapDomain A A (fun z : F => z.1)).comp
    (Finsupp.lmapDomain A A (fun e : E => (⟨e.1, hEF e.2⟩ : F))))
    (restrictToStage E x hx) = _
  rw [← Finsupp.lmapDomain_comp]
  simpa [Function.comp_def, stageEmbedding_restrict E x hx] using
    (stageEmbedding_restrict F x (hx.trans hEF)).symm

/-- A compatible family of algebra maps out of all finite stages descends uniquely to the
set-indexed divided power polynomial algebra. -/
@[stacks 07H6 "set_indexed_divided_power_polynomial_algebra"]
public theorem finiteStageInclusion_existsUnique_lift (A : Type u) [CommRing A]
    (W : Type w) (B : Type*) [CommRing B] [Algebra A B]
    (f : (E : Finset W) → DividedPowerAlgebra A (E →₀ A) →ₐ[A] B)
    (hf : ∀ (E F : Finset W) (h : E ⊆ F),
      (f F).comp (finiteStageMap A h) = f E) :
    ∃! g : setIndexedDividedPowerPolynomialAlgebra A W →ₐ[A] B,
      ∀ E : Finset W, g.comp (finiteStageInclusion A E) = f E := by
  classical
  let q : ℕ × (W →₀ A) → B := fun nx =>
    f nx.2.support (DividedPowerAlgebra.dp A nx.1
      (restrictToStage nx.2.support nx.2 (by simp)))
  have q_stage (n : ℕ) (x : W →₀ A) (E : Finset W) (hx : x.support ⊆ E) :
      q (n, x) = f E (DividedPowerAlgebra.dp A n (restrictToStage E x hx)) := by
    have h := AlgHom.congr_fun (hf x.support E hx)
      (DividedPowerAlgebra.dp A n (restrictToStage x.support x subset_rfl))
    rw [AlgHom.comp_apply, finiteStageMap, DividedPowerAlgebra.map_apply_dp,
      restrict_transition hx x (by simp)] at h
    simpa [q] using h.symm
  let φ := DividedPowerAlgebra.lift' (R := A) (M := W →₀ A) (A := B)
    (f := q)
    (by
      intro x
      rw [q_stage 0 x x.support (by simp)]
      simp [restrictToStage, DividedPowerAlgebra.dp_zero])
    (by
      intro n a x
      have hs : (a • x).support ⊆ x.support := Finsupp.support_smul
      rw [q_stage n (a • x) x.support hs, q_stage n x x.support (by simp)]
      have hres : restrictToStage x.support (a • x) hs =
          a • restrictToStage x.support x (by simp) := by
        ext y
        change (a • x) y.1 = a * x y.1
        simp [Finsupp.smul_apply]
      rw [hres, DividedPowerAlgebra.dp_smul]
      simp [map_smul])
    (by
      intro n p x
      rw [q_stage n x x.support (by simp), q_stage p x x.support (by simp),
        q_stage (n + p) x x.support (by simp)]
      simpa using congrArg (f x.support)
        (DividedPowerAlgebra.dp_mul (R := A) (n := n) (p := p)
          (m := restrictToStage x.support x (by simp))))
    (by
      intro n x y
      let E := x.support ∪ y.support
      have hx : x.support ⊆ E := Finset.subset_union_left
      have hy : y.support ⊆ E := Finset.subset_union_right
      have hxy : (x + y).support ⊆ E := Finsupp.support_add
      rw [q_stage n (x + y) E hxy]
      have hres : restrictToStage E (x + y) hxy =
          restrictToStage E x hx + restrictToStage E y hy := by ext z; rfl
      rw [hres, DividedPowerAlgebra.dp_add, map_sum]
      refine Finset.sum_congr rfl ?_
      rintro ⟨k, l⟩ -
      rw [map_mul, ← q_stage k x E hx, ← q_stage l y E hy])
  have hφ (E : Finset W) : φ.comp (finiteStageInclusion A E) = f E := by
    refine DividedPowerAlgebra.algHom_ext fun n m => ?_
    have hx : (Finsupp.lmapDomain A A (fun e : E => e.1) m).support ⊆ E := by
      rw [Finsupp.lmapDomain_apply]
      exact Finsupp.mapDomain_support.trans (Finset.image_subset_iff.mpr fun e _ => e.2)
    rw [AlgHom.comp_apply, finiteStageInclusion, DividedPowerAlgebra.map_apply_dp]
    simp only [φ, DividedPowerAlgebra.lift'_apply_dp]
    rw [q_stage n _ E hx]
    unfold restrictToStage
    rw [Finsupp.lmapDomain_apply]
    exact congrArg (fun z => f E (DividedPowerAlgebra.dp A n z))
      (Finsupp.comapDomain_mapDomain (f := Subtype.val) Subtype.val_injective m)
  refine ⟨φ, hφ, fun g hg => DividedPowerAlgebra.algHom_ext fun n x => ?_⟩
  simpa only [AlgHom.comp_apply, finiteStageInclusion, DividedPowerAlgebra.map_apply_dp,
    stageEmbedding_restrict] using
    AlgHom.congr_fun ((hg x.support).trans (hφ x.support).symm)
      (DividedPowerAlgebra.dp A n (restrictToStage x.support x subset_rfl))

add_to_stacks 07H6 "set_indexed_divided_power_polynomial_algebra"
  DividedPowers.dividedPowerPolynomialIdeal

end DividedPowers
