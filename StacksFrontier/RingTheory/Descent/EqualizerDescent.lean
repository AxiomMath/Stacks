module

public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# Descent from an equalizer presentation of the descended module

Effectivity of flat descent, `Module.Descent.Datum.isBaseChange`, identifies an `S`-module
carrying a descent datum with the base change of the submodule the datum cuts out.  A descent
datum arising geometrically comes instead with another module together with a map into `N`, and
the information that the map is injective with image exactly the locus where two comparisons
agree.  For a module of sections on a covering of
an affine base that information is the sheaf axiom, and the two comparisons are the two
restrictions to the double overlap, so this is the shape in which descent is applied.

This file converts that shape into the base-change comparison at the base.  Nothing is assumed
about how the equalizer description arises: the hypothesis is that membership in the descended
module is equivalent to being a value of the given map, which is what the sheaf axiom supplies
once the double-overlap comparison has identified the coaction, and the conclusion is that the
map exhibits `N` as the base change of its source.

Three auxiliary statements are also proved.  The two axioms of a descent datum
are reduced to the comparisons on the double and the triple overlap: the counit axiom to the
existence of a retraction of the comparison, which geometrically is restriction along the
diagonal, and the cocycle axiom to an equality of two composites, which geometrically is
functoriality of restriction.  Both axioms thereby become statements about restriction maps
rather than computations with tensor products.  And `IsBaseChange` is converted into bijectivity
of `LinearMap.liftBaseChange`, the converse of the implication producing an `IsBaseChange` from
such a bijection.

## Main results

* `Module.Descent.counit_coaction_of_retraction`: **the counit axiom of a descent datum from a
  retraction of the comparison.**
* `Module.Descent.coassoc_of_comparison`: **the cocycle axiom of a descent datum from a
  comparison on the triple overlap.**
* `IsBaseChange.bijective_liftBaseChange`: **the base change of a map exhibiting its target as a
  base change is bijective.**
* `Module.Descent.Datum.equivDescended`: an injective map whose values are exactly the elements
  of the descended module is an isomorphism onto it.
* `Module.Descent.Datum.isBaseChange_of_mem_descended_iff`,
  `Module.Descent.Datum.bijective_liftBaseChange_of_mem_descended_iff` and
  `Module.Descent.Datum.exists_baseChangeEquiv_of_mem_descended_iff`: **an injective map whose
  values are exactly the elements of the descended module exhibits `N` as the base change of its
  source along a flat ring map**, in three equivalent forms.

## Implementation notes

The hypothesis is stated as `∀ n, n ∈ d.descended ↔ n ∈ LinearMap.range ρ` rather than as an
equality of submodules, because that is the form
`Module.Descent.Datum.mem_descended_iff_of_comparison` produces: it describes membership in the
descended module by an equation between two maps out of `N`, and a sheaf axiom describes the
same locus as the image of the restriction from the base, and the two descriptions combine by
composing two equivalences of memberships.

No faithful flatness is needed: flatness of `S` over `R` is what effectivity of descent asks
for, and the injectivity and surjectivity of `ρ` onto the descended module are hypotheses rather
than consequences.  Under these hypotheses the values of `ρ` span `N` over `S`, by
`Module.Descent.span_range_eq_top_of_descended_le`.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open TensorProduct

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

namespace Module.Descent

/-- **The counit axiom of a descent datum from a retraction of the comparison.**  Let `c` be a
candidate coaction on `N`, let `e` identify `S ⊗[R] N` with a module `N₂` and let `p` be the
composite of `c` with that identification.  A retraction `r` of `p` which carries `e` to the
counit forces `c` to be counital.

For a module of sections this says that the coaction given by restriction along a projection of
the double overlap is counital because the diagonal is a section of that projection: `r` is
restriction along the diagonal, `hrp` is functoriality of restriction and `hre` says that the
diagonal is compatible with the identification. -/
theorem counit_coaction_of_retraction {N₂ : Type*} [AddCommGroup N₂] [Module R N₂]
    (c : N →ₗ[S] S ⊗[R] N) (e : S ⊗[R] N →ₗ[R] N₂) (p : N →ₗ[R] N₂)
    (hp : ∀ n, p n = e (c n)) (r : N₂ →ₗ[R] N) (hrp : ∀ n, r (p n) = n)
    (hre : ∀ x, r (e x) = counit R S N x) (n : N) :
    counit R S N (c n) = n := by
  rw [← hre, ← hp, hrp]

/-- **The cocycle axiom of a descent datum from a comparison on the triple overlap.**  Let `c` be
a candidate coaction on `N`, let `e` identify `S ⊗[R] N` with a module `N₂`, let `p` be the
composite of `c` with that identification, and let `e₃` identify `S ⊗[R] (S ⊗[R] N)`
injectively with a module `N₃` in such a way that the two maps whose equality on `c n` the
cocycle axiom asserts are induced by maps `u` and `v` out of `N₂`.  Then the axiom follows from
the equality of the two composites `u ∘ p` and `v ∘ p`.

For a module of sections `N₂` and `N₃` are the sections over the double and triple overlaps, `u`
and `v` are the restrictions along the two projections of the triple overlap which factor
through the double overlap, and the equality of the composites is functoriality of restriction:
both composites are restriction along the same morphism.  This is why a descent datum obtained
from restriction maps is automatically a cocycle, and the lemma isolates that fact from the
tensor calculus. -/
theorem coassoc_of_comparison {N₂ N₃ : Type*} [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃]
    [Module R N₃] (c : N →ₗ[S] S ⊗[R] N) (e : S ⊗[R] N →ₗ[R] N₂) (p : N →ₗ[R] N₂)
    (hp : ∀ n, p n = e (c n)) (e₃ : S ⊗[R] (S ⊗[R] N) →ₗ[R] N₃)
    (he₃ : Function.Injective e₃) (u v : N₂ →ₗ[R] N₃)
    (hu : ∀ x, e₃ (AlgebraTensorModule.lTensor S S (c.restrictScalars R) x) = u (e x))
    (hv : ∀ x, e₃ (AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1) x) = v (e x))
    (huv : ∀ n, u (p n) = v (p n)) (n : N) :
    AlgebraTensorModule.lTensor S S (c.restrictScalars R) (c n) =
      AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1) (c n) :=
  he₃ (by rw [hu, hv, ← hp, huv])

end Module.Descent

/-- **The base change of a map exhibiting its target as a base change is bijective.**  This is
the converse of the implication used to produce an `IsBaseChange` from a bijection. -/
theorem IsBaseChange.bijective_liftBaseChange {M : Type*} [AddCommGroup M] [Module R M]
    {ρ : M →ₗ[R] N} (h : IsBaseChange S ρ) :
    Function.Bijective (ρ.liftBaseChange S) := by
  have he : (ρ.liftBaseChange S : S ⊗[R] M → N) = h.equiv := by
    refine funext fun x => ?_
    induction x with
    | tmul s m => rw [LinearMap.liftBaseChange_tmul, h.equiv_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [he]
  exact h.equiv.bijective

namespace Module.Descent.Datum

variable (d : Datum R S N) {M : Type*} [AddCommGroup M] [Module R M] (ρ : M →ₗ[R] N)

/-- **An injective map whose values are exactly the elements of the descended module is an
isomorphism onto it.** -/
noncomputable def equivDescended (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, n ∈ d.descended ↔ n ∈ LinearMap.range ρ) : M ≃ₗ[R] d.descended :=
  LinearEquiv.ofBijective (LinearMap.codRestrict d.descended ρ fun m => (hmem (ρ m)).2 ⟨m, rfl⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun n => by
      obtain ⟨m, hm⟩ := (hmem n.1).1 n.2
      exact ⟨m, Subtype.ext hm⟩⟩

/-- `Module.Descent.Datum.equivDescended` is `ρ` itself. -/
@[simp]
lemma coe_equivDescended (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, n ∈ d.descended ↔ n ∈ LinearMap.range ρ) (m : M) :
    (d.equivDescended ρ hinj hmem m : N) = ρ m := rfl

variable [Module.Flat R S]

/-- **Descent from an equalizer presentation of the descended module.**  An injective map into
`N` whose values are exactly the elements of the module descended from a descent datum exhibits
`N` as the base change of its source along a flat ring map.

For a module of sections on a covering of an affine base the map is the restriction from the
base, the injectivity and the description of the image are the sheaf axiom, and the conclusion is
the base-change comparison for the sections over the base. -/
theorem isBaseChange_of_mem_descended_iff (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, n ∈ d.descended ↔ n ∈ LinearMap.range ρ) :
    IsBaseChange S ρ := by
  have hρ : ρ = d.descended.subtype ∘ₗ (d.equivDescended ρ hinj hmem).toLinearMap :=
    LinearMap.ext fun _ => rfl
  rw [hρ]
  exact IsBaseChange.comp_equiv _ _ d.isBaseChange

/-- `Module.Descent.Datum.isBaseChange_of_mem_descended_iff` as bijectivity of the base change of
`ρ`. -/
theorem bijective_liftBaseChange_of_mem_descended_iff (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, n ∈ d.descended ↔ n ∈ LinearMap.range ρ) :
    Function.Bijective (ρ.liftBaseChange S) :=
  (d.isBaseChange_of_mem_descended_iff ρ hinj hmem).bijective_liftBaseChange

/-- `Module.Descent.Datum.isBaseChange_of_mem_descended_iff` as a linear equivalence carrying
`1 ⊗ₜ m` to `ρ m`. -/
theorem exists_baseChangeEquiv_of_mem_descended_iff (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, n ∈ d.descended ↔ n ∈ LinearMap.range ρ) :
    ∃ eq : S ⊗[R] M ≃ₗ[S] N, ∀ m : M, eq ((1 : S) ⊗ₜ[R] m) = ρ m :=
  ⟨(d.isBaseChange_of_mem_descended_iff ρ hinj hmem).equiv, fun m => by
    rw [IsBaseChange.equiv_tmul, one_smul]⟩

end Module.Descent.Datum

end
