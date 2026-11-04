module

public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Finitely many separable closed points detecting global functions

Let `X` be smooth and proper over a field `k` and let `U ⊆ X` be a dense open subscheme. Then
there are finitely many closed points `x₁, …, x_m` of `X`, all lying in `U` and all with finite
separable residue field over `k`, such that a global function on `X` vanishing at every `xⱼ` is
zero.

The ring `A = Γ(X, 𝒪_X)` is finite over `k` (Stacks 0BUG (1)) and reduced, so it is the product of
its residue fields at its finitely many maximal ideals `𝔪`. For each `𝔪` the idempotent `e_𝔪`
projecting onto `A/𝔪` has nonempty non-vanishing locus `X_{e_𝔪}`, at every point of which the
kernel of evaluation is `𝔪`; this open meets `U`, and by Stacks 056U it contains a closed point
with finite separable residue field. A function vanishing at all these points lies in every `𝔪`,
hence is zero.

This is the choice of points in the proof of Stacks 0FIS, made in every connected component of
the blowup at once rather than after reducing to a connected `X`.

## Main results

* `AlgebraicGeometry.exists_separableClosedPoints_injective_Γevaluation`.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Finitely many separable closed points in a dense open detect global functions.** For `X`
smooth and proper over a field `k` and `U ⊆ X` dense open, there are finitely many closed points
of `X` in `U`, each with finite separable residue field over `k`, such that evaluation at them is
injective on `Γ(X, 𝒪_X)`. -/
theorem exists_separableClosedPoints_injective_Γevaluation {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] (U : X.Opens)
    (hU : Dense (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (x : ι → X),
      (∀ j, x j ∈ U ∧ x j ∈ closedPoints X ∧
        letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x j)).hom.toAlgebra
        Module.Finite k (X.residueField (x j)) ∧ Algebra.IsSeparable k (X.residueField (x j))) ∧
      Function.Injective fun s : Γ(X, ⊤) => fun j => (X.Γevaluation (x j)).hom s := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  classical
  have : Module.Finite k Γ(X, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k f
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  have : IsReduced X := isReduced_of_smooth f
  have : _root_.IsReduced Γ(X, ⊤) := inferInstance
  let A := Γ(X, ⊤)
  let φ := IsArtinianRing.equivPi A
  -- the idempotent of the factor at `𝔪`
  let e : MaximalSpectrum A → A := fun m => φ.symm (Pi.single m 1)
  have he : ∀ m m' : MaximalSpectrum A, Ideal.Quotient.mk m'.asIdeal (e m) =
      (Pi.single m 1 : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) m' := fun m m' =>
    congrFun (φ.apply_symm_apply (Pi.single m 1)) m'
  -- the kernel of evaluation at `y ∈ X_{e_𝔪}` is `𝔪`
  have hker : ∀ (m : MaximalSpectrum A) (y : X), y ∈ X.basicOpen (e m) →
      ∀ s : A, (X.Γevaluation y).hom s = 0 → s ∈ m.asIdeal := by
    intro m y hy s hs
    let P := RingHom.ker (X.Γevaluation y).hom
    have : P.IsPrime := RingHom.ker_isPrime _
    have : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
    have hem : e m ∉ P :=
      (X.evaluation_ne_zero_iff_mem_basicOpen y (Set.mem_univ _) (e m)).mpr hy
    by_cases hPm : P = m.asIdeal
    · exact hPm ▸ hs
    · refine (hem ?_).elim
      have h0 := he m ⟨P, inferInstance⟩
      rw [Pi.single_eq_of_ne (fun h : (⟨P, inferInstance⟩ : MaximalSpectrum A) = m =>
        hPm (congrArg MaximalSpectrum.asIdeal h))] at h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  -- choose a point in each `U ∩ X_{e_𝔪}`
  have hdense := dense_closedPoints_with_finite_separable_residueField_of_smooth f
  have hpt : ∀ m : MaximalSpectrum A, ∃ y : X, y ∈ U ∧ y ∈ X.basicOpen (e m) ∧ y ∈ closedPoints X ∧
      let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation y).hom.toAlgebra
      Module.Finite k (X.residueField y) ∧ Algebra.IsSeparable k (X.residueField y) := by
    intro m
    have hne : e m ≠ 0 := by
      intro h0
      have := he m m
      rw [h0, map_zero, Pi.single_eq_same] at this
      exact zero_ne_one this
    have hbo : (X.basicOpen (e m) : Set X).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hne ((basicOpen_eq_bot_iff (e m)).mp (SetLike.coe_injective (by simpa using hemp)))
    obtain ⟨z, hzU, hzb⟩ := hU.inter_open_nonempty _ (X.basicOpen (e m)).isOpen hbo
    obtain ⟨y, hyO, hy⟩ := hdense.inter_open_nonempty ((U : Set X) ∩ X.basicOpen (e m))
      (U.isOpen.inter (X.basicOpen (e m)).isOpen) ⟨z, hzb, hzU⟩
    exact ⟨y, hyO.1, hyO.2, hy.1, hy.2⟩
  choose x hxU hxb hxc hxfs using hpt
  refine ⟨MaximalSpectrum A, inferInstance, x, fun m => ⟨hxU m, hxc m, hxfs m⟩,
    fun s t hst => φ.injective (funext fun m => ?_)⟩
  show Ideal.Quotient.mk m.asIdeal s = Ideal.Quotient.mk m.asIdeal t
  rw [Ideal.Quotient.eq]
  refine hker m (x m) (hxb m) _ ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hst m

end AlgebraicGeometry

end
