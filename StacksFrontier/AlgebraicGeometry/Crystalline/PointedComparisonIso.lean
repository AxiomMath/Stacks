module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PointedTaylorComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormula

/-!
# The comparisons of [Stacks, Tag 07JH] are isomorphisms

After the cocycle identity, the proof of [Stacks, Proposition 60.17.4, Tag 07JH] concludes:

> It is also true that `c_{f, f} = 1`.  Hence these maps are all isomorphisms and we see that the
> module `ℱ_T` is independent of the choice of `f`.

Both inputs of that sentence are in the library — `c_{f,f} = 1` is
`Crystalline.pointedComparison_self` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean` and the cocycle is
`Crystalline.pointedComparison_comp_eq` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedTaylorComparison.lean` — and the conclusion
drawn from them is not.  The module documentation of that second file records the gap exactly:

> What this does not give is independence of the choice of pointing on the *unpointed* site: that
> needs the comparisons to be isomorphisms, for which `c_{f,f} = 1` and this identity are the two
> inputs.

This module draws the conclusion.

## The one new ingredient

The cocycle is stated for three pointings `f, g, h` and a map `T₃` carrying the series of
`ξ_{f,h}`; to take `h = f` one needs a `T₃` carrying the series of `ξ_{f,f}`, which is the series
of the **zero** family.  That is `Crystalline.hasPointedTaylorSum_pointedUnitComparison` below: at
one pointing the differences vanish, `Crystalline.taylorMonomial_zero_family` kills every
coefficient away from the empty multi-index, and what is left is the degree-zero term `1 ⊗ m`,
which is `Crystalline.pointedUnitComparison`.

It needs no convergence hypothesis.  The series has **one** possibly nonzero term, so
`Crystalline.hasTaylorSum_of_eq_zero` applies over the singleton `{0}` with no nilpotence of `p`
and no quasi-nilpotence: this is the same shape as the rest of the degenerate case, where the
whole series collapses to its constant term.

## Main results

* `Crystalline.hasPointedTaylorSum_pointedUnitComparison` — **at one pointing the Taylor series is
  its degree-zero term**: `m ↦ 1 ⊗ m` carries the series of `ξ_{f,f} = 0`, with no hypothesis
  beyond `θ_0 = id`.
* `Crystalline.pointedComparison_comp_eq_id` — **`c_{g,f} ∘ c_{f,g} = 1`**: the composite of the
  comparisons of two pointings, in the two orders, is the identity.  This is the source's "Hence
  these maps are all isomorphisms".
* `Crystalline.pointedComparisonEquiv` — **`c_{f,g}` as a `B`-linear equivalence
  `M ⊗_{D,f} B ≃ M ⊗_{D,g} B`**, which is the source's "the module `ℱ_T` is independent of the
  choice of `f`".
* `Crystalline.bijective_pointedComparison` — the same, as bijectivity of the map.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
The tag is an equivalence of categories; this module makes one family of comparison maps
invertible.

What it does **not** do is the descent along the forgetful functor from the pointed site.
Invertibility plus the cocycle makes the pointings of a fixed object into a connected system of
isomorphic modules, which is what descent consumes; the descent itself is
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedDescent.lean`, where the descended module is
the module of compatible families over all pointings and this invertibility is what makes
evaluation at any one of them an isomorphism.  That module reaches the unpointed algebraic site
`CRIS(C/A)` and no further: the passage from a module over the section ring to a quasi-coherent
sheaf on `Cris(X/S)` is in neither module.  The two other verifications the source omits are in
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorRestrictionIndependence.lean` (the restriction
maps do not depend on the pointing) and
`StacksFrontier/AlgebraicGeometry/Crystalline/PairCrystalCondition.lean` (the crystal condition for
the assignment).

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u uI v w

namespace Crystalline

section Iso

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M] (p : ℕ) {ι : Type uI} [DecidableEq ι] {theta : ι → (M → M)}
  {thetaPow : (ι →₀ ℕ) → (M → M)}

omit [DecidableEq ι] in
/-- **At one pointing the Taylor series of [Stacks, Tag 07JH] is its degree-zero term.**

The differences `ξ_{f,f}` vanish (`Crystalline.pointedDiff_self`), so by
`Crystalline.taylorMonomial_zero_family` every coefficient away from the empty multi-index is
zero, and `Crystalline.hasTaylorSum_of_eq_zero` over the singleton `{0}` gives convergence to the
one remaining term `1 ⊗ θ_0(m) = 1 ⊗ m`.

This is the `T₃` that `Crystalline.pointedComparison_comp_eq` needs in order to be read at
`h = f`, and it is where `Crystalline.pointedUnitComparison` is identified as a Taylor comparison
rather than merely a semilinear map.  No nilpotence of `p` and no quasi-nilpotence enter: the
series is finite because it has a single term. -/
theorem hasPointedTaylorSum_pointedUnitComparison (f : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hzero : thetaPow 0 = id) (m : M) :
    HasPointedTaylorSum M p thetaPow f (pointedDiff f f x) m (pointedUnitComparison M f m) := by
  classical
  let := pointedAlgebra f
  have hterms : ∀ K ∉ ({0} : Finset (ι →₀ ℕ)),
      taylorMonomial X.ring (pointedDiff f f x) K ⊗ₜ[Dt.ring.carrier] thetaPow K m = 0 := by
    intro K hK
    rw [pointedDiff_self, taylorMonomial_zero_family X.ring (by simpa using hK),
      TensorProduct.zero_tmul]
  have h := hasTaylorSum_of_eq_zero p Dt.ring X.ring M thetaPow (pointedDiff f f x) m
    ({0} : Finset (ι →₀ ℕ)) hterms
  rw [Finset.sum_singleton, taylorMonomial_zero, hzero, id_eq] at h
  exact h

omit [DecidableEq ι] in
/-- **The source's "Hence these maps are all isomorphisms": `c_{g,f} ∘ c_{f,g} = 1`.**

This is `Crystalline.pointedComparison_comp_eq` read at the third pointing `h = f`, where the
cocycle's right-hand side is the comparison of `ξ_{f,f} = 0`.  By
`Crystalline.hasPointedTaylorSum_pointedUnitComparison` the degree-zero map
`Crystalline.pointedUnitComparison` carries that series, so the cocycle identifies the composite
with `c_{f,f}`, and `Crystalline.pointedComparison_self` says that is the identity.

The hypotheses are those of the cocycle and nothing more: `hDt`, the composite coordinate
operators of the module, nilpotence of `p` in `B` — [Stacks, Tag 07HM] for every object of
`Cris(X/S)` — the two comparison data and the source's own finiteness of the surviving
multi-indices. -/
theorem pointedComparison_comp_eq_id (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X)
    (x : ι → Dt.ring.carrier) (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom f))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow f (pointedDiff g f x) m (T₂ m))
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    (pointedComparison M g f T₂).comp (pointedComparison M f g T₁) = LinearMap.id := by
  classical
  rw [pointedComparison_comp_eq M p hDt f g f x hfamM hpB T₁ T₂ (pointedUnitComparison M f)
      hT₁ hT₂ (fun m ↦ hasPointedTaylorSum_pointedUnitComparison M p f x hfamM.1 m) hfin,
    pointedComparison_self]

omit [DecidableEq ι] in
/-- **The comparison of two pointings is bijective.**  Both composites are the identity, by
`Crystalline.pointedComparison_comp_eq_id` in the two orders, so `c_{f,g}` is injective with a
left inverse and surjective with a right inverse. -/
theorem bijective_pointedComparison (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X)
    (x : ι → Dt.ring.carrier) (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom f))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow f (pointedDiff g f x) m (T₂ m))
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    Function.Bijective (pointedComparison M f g T₁) := by
  have h₁ := pointedComparison_comp_eq_id M p hDt f g x hfamM hpB T₁ T₂ hT₁ hT₂ hfin
  have h₂ := pointedComparison_comp_eq_id M p hDt g f x hfamM hpB T₂ T₁ hT₂ hT₁ hfin
  exact ⟨Function.LeftInverse.injective (g := pointedComparison M g f T₂)
      (LinearMap.congr_fun h₁),
    Function.RightInverse.surjective (g := pointedComparison M g f T₂)
      (LinearMap.congr_fun h₂)⟩

/-- **`ℱ_T` is independent of the choice of `f`**, the conclusion of this paragraph of the proof of
[Stacks, Proposition 60.17.4, Tag 07JH]: the comparison `c_{f,g}` is a `B`-linear **equivalence**

`M ⊗_{D,f} B ≃ M ⊗_{D,g} B`.

Its inverse is `c_{g,f}`, by `Crystalline.pointedComparison_comp_eq_id`.  Together with the
cocycle this makes the modules attached to the pointings of one object of `Cris(X/S)` a single
module up to canonical isomorphism, which is the statement the source's construction of `ℱ_T`
rests on. -/
noncomputable def pointedComparisonEquiv (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom f))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow f (pointedDiff g f x) m (T₂ m))
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    pointedSections M (pointedOfHom f) ≃ₗ[X.ring.carrier] pointedSections M (pointedOfHom g) :=
  LinearEquiv.ofBijective (pointedComparison M f g T₁)
    (bijective_pointedComparison M p hDt f g x hfamM hpB T₁ T₂ hT₁ hT₂ hfin)

omit [DecidableEq ι] in
/-- The equivalence `Crystalline.pointedComparisonEquiv` acts on an element `z` as the
comparison map `c_{f,g}`. -/
@[simp] theorem pointedComparisonEquiv_apply (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom f))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow f (pointedDiff g f x) m (T₂ m))
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite)
    (z : pointedSections M (pointedOfHom f)) :
    pointedComparisonEquiv M p hDt f g x hfamM hpB T₁ T₂ hT₁ hT₂ hfin z =
      pointedComparison M f g T₁ z := rfl

end Iso

end Crystalline

end
