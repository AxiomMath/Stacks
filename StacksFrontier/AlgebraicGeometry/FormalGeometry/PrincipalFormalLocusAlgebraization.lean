module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExactMiddle
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusImprovement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusSupported
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusSurjectivity
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.RingTheory.Dualizing.FormalFibresSerreOne

/-!
# Algebraization of formal sections at a principal formal locus: Stacks 0H49

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A`, let `U = Spec(A) ∖ V(𝔞)` and let `ℱ` be a coherent
module on `U`. Stacks 0H49 asserts that if `A` is `f`-adically complete and has a dualizing
complex, and every associated point `x` of `ℱ` outside `V(f)` whose closure meets `V(f)` outside
`V(𝔞)` has `dim(𝒪_{closure{x}, z}) > 2` for every `z ∈ closure{x} ∩ V(𝔞)`, then the comparison
map

`colim_V Γ(V, ℱ) ⟶ lim Γ(U, ℱ / fⁿ ℱ)`

is an isomorphism, the colimit running over the opens `V ⊆ U` containing `U ∩ V(f)`. This file
proves it, and registers the tag on
`Stacks.Algebraization.isIso_comparisonMap_span_singleton_of_two_lt_closureLocalDimension`.

## The argument

The proof follows the shape of the source's first proof — improve `ℱ` along `V(f) ∩ U`, prove
the claim for the improvement by Stacks 0EIH, and pass back along short exact sequences by
Stacks 0H48 — with one change, forced by Stacks 0DX5. As stated, Stacks 0DX5 is false: on
`X = 𝔸⁵ = Spec k[a,b,c,d,e]` take `S = V(a,b) ∪ V(c,d)` (two `3`-planes meeting in the line
`C = V(a,b,c,d)`), `H = V(b,c,d,e)` (a line meeting `C` in the origin `p` only), `ℱ = 𝒪_S ⊕ 𝒪_H`
and `Z = C`. The origin is an immediate specialization of the generic point of `H`, so condition
(2) of 0DX5 asks `ℱ_p → ℱ''_p` to be surjective; as `ℱ` has no section supported on `Z`, the map
`ℱ → ℱ''` is injective, hence an isomorphism at `p` and so on a neighbourhood of `p`, which
contains the generic point `η` of `C`. But `η` is reached from no associated point of `ℱ` by an
immediate specialization (it has codimension `2` in both planes), so condition (3) asks
`depth(ℱ''_η) ≥ 2`, while `depth(ℱ_η) = depth(𝒪_{S,η}) = 1` (two planes meeting in a point).
The first proof of 0H49 uses 0DX5 through its observation (3), that every associated point of
`ℱ'/fℱ'` is an immediate specialization of an associated point of `ℱ`, which rests on exactly
these two clauses, so that observation is not available as stated.

So the module is first split by its associated points. A coherent module with an associated
point off `V(f)` is the middle term of `0 → ℱ' → ℱ → ℱ'' → 0` where `ℱ''` is the depth-one
quotient (Stacks 0DX3) of `ℱ` along `V(f)` and the closures of the other associated points off
`V(f)`, taken at a minimal one `x₀`; then `ℱ''` has the single associated point `x₀` and `ℱ'`
fewer associated points off `V(f)`. For a module with the single associated point `x₀ ∉ V(f)`
the improvement is a pushforward from the complement of the closures of the depth-one points of
`V(f) ∩ U` that are not immediate specializations of `x₀`, as in
`Stacks.Algebraization.exists_shortExact_isCoherent_pushforward_of_associatedPoints_eq_singleton`;
these closures avoid the immediate specializations of `x₀`, which is what the single associated
point buys. The improvement satisfies the hypotheses of Stacks 0EIH in sheaf form
(`Stacks.Algebraization.isIso_comparisonMap_span_singleton_of_isCoherent_pushforward`), its
cokernel is supported on `V(f) ∩ U`
(`Stacks.Algebraization.isIso_comparisonMap_of_associatedPoints_le`),
and the two clauses of Stacks 0H48 assemble the conclusion, by induction on the number of
associated points off `V(f)`.

## Main results

* `Stacks.Algebraization.exists_shortExact_associatedPoints_subset_singleton` — the splitting by
  associated points.
* `Stacks.Algebraization.isIso_comparisonMap_span_singleton_of_associatedPoints` — the
  induction, with universal catenarity and `(S₁)` formal fibres in place of the dualizing
  complex.
* `Stacks.Algebraization.isIso_comparisonMap_span_singleton_of_two_lt_closureLocalDimension` —
  **Stacks 0H49**.

## References

* [Stacks Project, Tag 0H49](https://stacks.math.columbia.edu/tag/0H49)
* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **The splitting by associated points.** A coherent module `F` on `U = Spec(A) ∖ V(𝔞)` with
an associated point off `V(I)` is the middle term of a short exact sequence
`0 → F' → F → F'' → 0` of coherent modules in which `F''` has a single associated point `x₀`,
itself an associated point of `F` off `V(I)`, and `F'` has strictly fewer associated points off
`V(I)` than `F`, all of them associated points of `F`.

`x₀` is chosen minimal among the associated points off `V(I)`, `F''` is the depth-one quotient of
Stacks 0DX3 along `V(I)` together with the closures of the other associated points off `V(I)`,
and `F'` is the kernel of the quotient map, whose stalk at `x₀` vanishes. -/
theorem exists_shortExact_associatedPoints_subset_singleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hne : (associatedPointsOffVanishing A I a F).Nonempty) :
    ∃ (F' F'' : (complementZeroLocus A a : Scheme).Modules) (i : F' ⟶ F) (p : F ⟶ F'')
      (w : i ≫ p = 0) (x₀ : (complementZeroLocus A a : Scheme)),
      (ShortComplex.mk i p w).ShortExact ∧ F'.IsCoherent ∧ F''.IsCoherent ∧
      x₀ ∈ Stacks.Divisors.associatedPoints F ∧ ¬ I ≤ x₀.1.asIdeal ∧
      Stacks.Divisors.associatedPoints F'' ⊆ {x₀} ∧
      Stacks.Divisors.associatedPoints F' ⊆ Stacks.Divisors.associatedPoints F ∧
      associatedRank A I a F' < associatedRank A I a F := by
  have hSfin : (associatedPointsOffVanishing A I a F).Finite :=
    finite_associatedPointsOffVanishing A I a F
  obtain ⟨x₀, hx₀S, hx₀min⟩ := Set.Finite.exists_minimalFor
    (fun x : (complementZeroLocus A a : Scheme) => x.1.asIdeal) _ hSfin hne
  -- the specialization-stable locus along which the torsion is removed
  let T : Set (complementZeroLocus A a : Scheme) := {z | I ≤ z.1.asIdeal ∨
    ∃ x ∈ associatedPointsOffVanishing A I a F, x ≠ x₀ ∧ x.1.asIdeal ≤ z.1.asIdeal}
  have hle : ∀ {z w : (complementZeroLocus A a : Scheme)}, z ⤳ w → z.1.asIdeal ≤ w.1.asIdeal :=
    fun h => (PrimeSpectrum.le_iff_specializes _ _).2 ((subtype_specializes_iff _ _).1 h)
  have hTstab : StableUnderSpecialization T := by
    intro z w hzw hz
    rcases hz with h | ⟨x, hx, hne, hxz⟩
    · exact Or.inl (h.trans (hle hzw))
    · exact Or.inr ⟨x, hx, hne, hxz.trans (hle hzw)⟩
  have hx₀T : x₀ ∉ T := by
    rintro (h | ⟨x, hx, hxne, hxle⟩)
    · exact hx₀S.2 h
    · exact hxne (Subtype.ext (PrimeSpectrum.ext (le_antisymm hxle (hx₀min hx hxle))))
  let F'' := depthOneQuotient (complementZeroLocus A a : Scheme) T hTstab F
  let g := toDepthOneQuotient (complementZeroLocus A a : Scheme) T hTstab F
  have hspec := depthOneQuotient_spec (complementZeroLocus A a : Scheme) T hTstab F
  have hF''c : F''.IsCoherent := hspec.1
  have _ : Epi g := hspec.2.1
  have hnotass : ∀ y, y ∈ T → y ∉ Stacks.Divisors.associatedPoints F'' := fun y hy =>
    Stacks.Divisors.notMem_associatedPoints_of_one_le_depth F'' y (hspec.2.2.2 y hy)
  have hsub : ∀ y, y ∈ Stacks.Divisors.associatedPoints F'' →
      y ∈ Stacks.Divisors.associatedPoints F := fun y hy =>
    (AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_iff_of_isIso_stalkFunctor_map
      g y (hspec.2.2.1 y (fun h => hnotass y h hy))).2 hy
  have hAss'' : Stacks.Divisors.associatedPoints F'' ⊆ {x₀} := by
    intro y hy
    by_contra hyne
    refine hnotass y ?_ hy
    by_cases hyI : I ≤ y.1.asIdeal
    · exact Or.inl hyI
    · exact Or.inr ⟨y, ⟨hsub y hy, hyI⟩, hyne, le_rfl⟩
  -- the kernel of the quotient map has a vanishing stalk at `x₀`, so loses `x₀`
  have hx₀notF' : x₀ ∉ associatedPointsOffVanishing A I a (kernel g) := by
    rintro ⟨hmem, -⟩
    have hgiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x₀).map g.mapPresheaf) :=
      hspec.2.2.1 x₀ hx₀T
    have hginj : Function.Injective
        (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL
          (complementZeroLocus A a : Scheme).toRingedSpace F.val F''.val g.val x₀) :=
      (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor Ab.{u} x₀).map g.mapPresheaf)).1
    let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule
      (complementZeroLocus A a : Scheme).toRingedSpace F.val x₀
    let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule
      (complementZeroLocus A a : Scheme).toRingedSpace F''.val x₀
    let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule
      (complementZeroLocus A a : Scheme).toRingedSpace (kernel g).val x₀
    have hkerinj := Stacks.SheafOfModules.TensorStalkRingedSpace.injective_stalkMapL_kernel_ι
      (X := (complementZeroLocus A a : Scheme).toRingedSpace) g x₀
    have hrange := Stacks.SheafOfModules.TensorStalkRingedSpace.range_stalkMapL_kernel_ι
      (X := (complementZeroLocus A a : Scheme).toRingedSpace) g x₀
    have hzero : ∀ m : TopCat.Presheaf.stalk (C := Ab.{u}) (kernel g).val.presheaf x₀, m = 0 :=
      fun m => (LinearMap.map_eq_zero_iff _ hkerinj).1 <|
        (LinearMap.map_eq_zero_iff _ hginj).1 <|
          LinearMap.mem_ker.1 (hrange.le (LinearMap.mem_range_self _ m))
    obtain ⟨hp, m, hm⟩ := hmem
    refine hp.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← hm]
    exact Submodule.mem_colon_span_singleton.2 (by simp [hzero m])
  have hlt : associatedRank A I a (kernel g) < associatedRank A I a F :=
    Set.ncard_lt_ncard
      ⟨associatedPointsOffVanishing_subset_of_mono A I a (kernel.ι g),
        fun hcon => hx₀notF' (hcon hx₀S)⟩ hSfin
  exact ⟨kernel g, F'', kernel.ι g, g, kernel.condition g, x₀,
    CategoryTheory.ShortComplex.shortExact_mk_kernel_ι g,
    _root_.SheafOfModules.kernel_isCoherent g, hF''c, hx₀S.1, hx₀S.2, hAss'',
    AlgebraicGeometry.associatedPoints_subset_of_mono (kernel.ι g), hlt⟩

/-- **The induction of the proof of Stacks 0H49.** Over a Noetherian, `f`-adically complete,
universally catenary ring whose local rings have `(S₁)` formal fibres, the comparison map of a
coherent module on `U = Spec(A) ∖ V(𝔞)` satisfying condition (2) of Stacks 0H49 is an
isomorphism; the induction is on the number `n` of associated points off `V(f)`. -/
theorem isIso_comparisonMap_span_singleton_of_associatedPoints
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hcat : Ring.IsUniversallyCatenary A)
    (hfib : ∀ (z : Spec (CommRingCat.of A))
      (q : PrimeSpectrum ((Spec (CommRingCat.of A)).presheaf.stalk z)),
      HasSerreCondition ((Spec (CommRingCat.of A)).completedLocalRing z
        ⊗[(Spec (CommRingCat.of A)).presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ∀ (n : ℕ) (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent],
      associatedRank A (Ideal.span {f}) a F = n →
      (∀ x : (complementZeroLocus A a : Scheme),
        x ∈ Stacks.Divisors.associatedPoints F → f ∉ x.1.asIdeal →
        (∃ y : PrimeSpectrum A,
          x.1.asIdeal ≤ y.asIdeal ∧ f ∈ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
        ∀ z : PrimeSpectrum A, x.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
          (2 : WithBot ℕ∞) < closureLocalDimension A x.1 z) →
      IsIso (comparisonMap A (Ideal.span {f}) a F) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ hn hdim
  by_cases hne : (associatedPointsOffVanishing A (Ideal.span {f}) a F).Nonempty
  · obtain ⟨F', F'', i, p, w, x₀, hS, hF', hF'', hx₀, hx₀I, hAss'', hAss', hlt⟩ :=
      exists_shortExact_associatedPoints_subset_singleton A (Ideal.span {f}) a F hne
    have hx₀f : f ∉ x₀.1.asIdeal := fun h =>
      hx₀I ((Ideal.span_singleton_le_iff_mem _).2 h)
    -- the quotient with one associated point
    have h'' : IsIso (comparisonMap A (Ideal.span {f}) a F'') := by
      obtain ⟨G, Q, j, q, w', hS', hG, hQ, hAssG, hAssQ, hcoh⟩ :=
        exists_shortExact_isCoherent_pushforward_of_associatedPoints_eq_singleton A a f hcat hfib
          F'' x₀ hAss'' hx₀f (hdim x₀ hx₀ hx₀f)
      have hGiso : IsIso (comparisonMap A (Ideal.span {f}) a G) :=
        isIso_comparisonMap_span_singleton_of_isCoherent_pushforward A a f hcomplete G hAssG hcoh
      have hQiso : IsIso (comparisonMap A (Ideal.span {f}) a Q) :=
        isIso_comparisonMap_of_associatedPoints_le A (Ideal.span {f}) a Q fun x hx =>
          (Ideal.span_singleton_le_iff_mem _).2 (hAssQ x hx)
      exact isIso_comparisonMap_first_of_middle_and_third A (Ideal.span {f}) a
        (ShortComplex.mk j q w') hS' hGiso hQiso
    -- the kernel, by induction
    have h' : IsIso (comparisonMap A (Ideal.span {f}) a F') :=
      ih _ (hn ▸ hlt) F' rfl fun x hx => hdim x (hAss' hx)
    exact isIso_comparisonMap_middle_of_ends A (Ideal.span {f}) a
      (ShortComplex.mk i p w) hS h' h''
  · refine isIso_comparisonMap_of_associatedPoints_le A (Ideal.span {f}) a F fun x hx => ?_
    by_contra h
    exact hne ⟨x, hx, h⟩

/-- **Stacks Project, Tag 0H49.** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `ℱ` be
a coherent module on `U = Spec(A) ∖ V(𝔞)`. Assume `A` is `f`-adically complete and has a
dualizing complex, and that whenever `x` is an associated point of `ℱ` with `f ∉ 𝔭_x`, whose
closure meets `V(f)` outside `V(𝔞)`, and `z ∈ closure{x} ∩ V(𝔞)`, the local ring of
`closure{x}` at `z` has dimension greater than two. Then the comparison map

`colim_V Γ(V, ℱ) ⟶ lim Γ(U, ℱ / fⁿ ℱ)`

is an isomorphism, the colimit being over the opens `V ⊆ U` containing `U ∩ V(f)`.

The closure of `x` in `Spec(A)` is `V(𝔭_x)`, so "`closure{x} ∩ V(f) ⊄ V(𝔞)`" is the existence
of a prime `y ⊇ 𝔭_x` with `f ∈ y` and `𝔞 ⊄ y`, and "`z ∈ closure{x} ∩ V(𝔞)`" is `𝔭_x ≤ z` and
`𝔞 ≤ z`. The dimension of `𝒪_{closure{x}, z}` is the Krull dimension of the primes of `A`
between `𝔭_x` and `z`, which is `Stacks.Algebraization.closureLocalDimension A 𝔭_x z`. No
hypothesis supplying the surjectivity half of Stacks 0EG2
(`Stacks.Algebraization.ComparisonSurjectivity`) is assumed.

The dualizing complex enters through its two consequences used by the source, universal
catenarity (Stacks 0A80) and Gorenstein, hence `(S₁)`, formal fibres (Stacks 0AWY); see the
module documentation for the rest of the argument. -/
@[stacks 0H49]
theorem isIso_comparisonMap_span_singleton_of_two_lt_closureLocalDimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A) (_hf : f ∈ a)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{v} A), Dualizing.IsDualizingComplex K)
    (hdimension : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F → f ∉ x.1.asIdeal →
      (∃ y : PrimeSpectrum A,
        x.1.asIdeal ≤ y.asIdeal ∧ f ∈ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, x.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        (2 : WithBot ℕ∞) < closureLocalDimension A x.1 z) :
    IsIso (comparisonMap A (Ideal.span {f}) a F) :=
  have ⟨hcat, hfib⟩ := isUniversallyCatenary_and_formalFibres_of_isDualizingComplex A hdualizing
  isIso_comparisonMap_span_singleton_of_associatedPoints A a f hcomplete hcat hfib _ F rfl
    hdimension

end Stacks.Algebraization

end
