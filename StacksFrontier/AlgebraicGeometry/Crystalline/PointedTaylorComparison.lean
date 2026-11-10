module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PairToCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCocycle
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormula
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorHausdorff

/-!
# The semilinear Taylor comparison for two pointings of one object

`Crystalline.pointedComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean` reads the comparison

`c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`

of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] off a semilinear map

`T : M →ₛₗ[f] M ⊗_{D,g} B`,

which it carries rather than constructs.  This module constructs it, from the existing Taylor
machinery and nothing else.

## The one obstruction, and why it is only a change of type

`Crystalline.HasTaylorSum` and `Crystalline.IsTwistedTaylorComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TwistedTaylorComparison.lean` state the Taylor series
in `B ⊗_D M` for *the* `D`-algebra structure on `B`, while the target of `c_{f,g}` is
`M ⊗_{D,g} B = TwistedScalars g ⊗_D M`, the base change along the second pointing.  The module
documentation of `StacksFrontier/AlgebraicGeometry/Crystalline/TwistedBaseChange.lean` records that
relating three divided power maps "needs that target generalised to `TwistedScalars h ⊗_D M`" and
that the generalisation "is now a change of type and nothing more".

That is exactly right, and it is even less than that: **no statement needs generalising at all.**
`Crystalline.TwistedScalars g` carries `g.toAlgebra` for its `D`-algebra structure, so

`TwistedScalars g ⊗_D M` *is* `B ⊗_D M` for the `Algebra D B` instance `g.toAlgebra`,

and the existing predicates read at that instance are already the twisted ones: a
`Crystalline.SecondDividedPowerMap` for it is a divided power map agreeing with `g` modulo `J_B`,
its `Crystalline.SecondDividedPowerMap.diffFamily` is the source's `ξ_i = f(x_i) - g(x_i)`, and
`Crystalline.IsTwistedTaylorComparison` for it is convergence to the values of an `f`-semilinear
map into `M ⊗_{D,g} B`.  `Crystalline.pointedAlgebra` names that instance, and everything below is
the existing theory applied at it.

## Main definitions

* `Crystalline.pointedAlgebra` — `B` as a `D`-algebra along the chosen map of a pointed object.
  This is the instance at which the existing Taylor machinery speaks about
  `Crystalline.pointedSections`.
* `Crystalline.HasPointedTaylorSum` — `Crystalline.HasTaylorSum` read at that instance: the
  series `∑_K ξ^{[K]} ⊗ θ_K(m)` converges to `t` in `M ⊗_{D,g} B`.
* `Crystalline.pointedDiff` — the source's family `ξ_{f,g} = f(x_i) - g(x_i)` for two pointings.
* `Crystalline.pointedDatum` — two pointings of one object, as the
  `Crystalline.SecondDividedPowerMap` of the second one's instance.

## Main results

* `Crystalline.exists_hasPointedTaylorSum` — **step one, the semilinear Taylor comparison for a
  pair**: an `f`-semilinear map `M →ₛₗ[f] M ⊗_{D,g} B` whose values are the sums of the Taylor
  series of `ξ_{f,g}`.  This is the map `Crystalline.pointedComparison` was carrying, and
  `Crystalline.exists_pointedComparison` reads it as the source's `c_{f,g}`: a `B`-linear map
  `M ⊗_{D,f} B ⟶ M ⊗_{D,g} B` sending `1 ⊗ m` to `∑_K ξ_{f,g}^{[K]} ⊗ θ_K(m)`.
* `Crystalline.hasPointedTaylorSum_eq_sum` — a pointed Taylor sum is the finite sum of the terms
  the quasi-nilpotence condition (07JE) leaves, by uniqueness
  (`Crystalline.hasTaylorSum_unique`).  This is what makes the composite computable.
* `Crystalline.hasPointedTaylorSum_pointedComparison_comp` — **step two, the cocycle at the Taylor
  level**: the composite `c_{g,h} ∘ c_{f,g}` carries the series of `ξ_{f,h}`.
* `Crystalline.pointedComparison_comp_eq` — **the cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}`** itself,
  from the previous item, `Crystalline.pointedComparison_comp` and uniqueness of the sum.  Both
  sides are the comparisons of the families the tag names, so this is the source's identity and
  not the weaker statement that the composite is *some* comparison.
* `Crystalline.pointedDiff_add_pointedDiff` — `ξ_{f,g} + ξ_{g,h} = ξ_{f,h}`, the coefficient
  identity the previous two items run on.
* `Crystalline.exists_Iic_thetaPow_mem_pPowSmul` — the surviving multi-indices are bounded by a
  `Finset.Iic`, so the series may be summed over a downward closed index set, which is what the
  cocycle `Crystalline.taylorComposite_prod_eq` needs.
* `Crystalline.taylorFormula_pointed_self` — **the one new hypothesis is satisfiable**: Taylor's
  formula in `B` holds at one pointing, where the coordinate differences vanish.  So
  `Crystalline.exists_hasPointedTaylorSum` is not the empty statement.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
The tag is an equivalence of categories; nothing here is about crystals, and the subject is one
semilinear map for one module.  Beyond that, the tag cannot be registered at all until a term of
`Crystalline.Reduction07JG` exists, and none does.

**Nothing of the Taylor theory is reproved.**  Every theorem below is an existing one applied at
`Crystalline.pointedAlgebra`: `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` for
the comparison, `Crystalline.hasTaylorSum_unique` for uniqueness,
`Crystalline.taylorComposite_prod_eq` for the cocycle, `Crystalline.hasTaylorSum_of_eq_zero` and
`Crystalline.taylorTerm_eq_zero_of_mem_pPowSmul` for convergence.  What is new is only that the
conclusions are about `Crystalline.pointedSections`, so that
`Crystalline.pointedComparison` and `Crystalline.pointedComparison_comp` apply to them.

**Hypotheses carried.**  None is assumed silently and each is the source's own or a named debt of
the chapter.

* `hDt` — surjectivity of `D → D/J_D ← C`, which holds because the fixed object is one of
  `Cris(C/A)` and not merely of `CRIS(C/A)`.  It is the hypothesis of
  `Crystalline.sub_pointRingHom_mem_ideal`, and it is what places `ξ_{f,g}` in `J_B`.
* `hfamM`, `hfamD`, `hthAdd`, `hleib` — the coordinate operators of the module and of the ring,
  their additivity, and the first-order Leibniz rule relating them.  These are the hypotheses of
  `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula`; see that theorem.
* `htay` — **Taylor's formula in `B`**, `f(a) = ∑_J g(∂_J a) ξ^{[J]}`.  This is the one remaining
  debt of the chapter's Taylor theory, identified as such in the module documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/TwistedTaylorComparison.lean`; it is discharged over
  a divided power polynomial algebra by `Crystalline.taylorFormula_polynomial`, and
  `Crystalline.taylorFormula_refl` shows it is satisfiable, so it is a hypothesis with content.
* `hpB` — `p^N = 0` in `B`, which [Stacks, Tag 07HM] requires of every divided power thickening;
  `Crystalline.DividedPowerThickening.prime_nilpotent` supplies it for every object of the site,
  which is what `Crystalline.exists_pointedComparison_of_thickening` uses.
* `hfin`, `hvanish` — the source's own "the sum is finite!", in the form
  `Crystalline.finite_thetaPow_notMem_pPowSmul` proves it from the quasi-nilpotence condition
  (07JE) of [Stacks, Tag 07JE].

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open scoped TensorProduct

universe u uI v w

namespace Crystalline

/-! ### The `D`-algebra structure along the chosen map of a pointed object -/

section Algebra

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S}

/-- **`B` as a `D`-algebra along the chosen divided power map of a pointed object.**  This is the
`Algebra D B` instance at which the Taylor theory of this chapter speaks about
`Crystalline.pointedSections`: the `D`-algebra structure of `Crystalline.TwistedScalars g` is
`g.toAlgebra`, so `TwistedScalars g ⊗_D M` is `B ⊗_D M` read at this instance, and no statement of
that theory needs to be generalised in order to reach the target of the comparison `c_{f,g}`.

It is not an instance: the whole point of `Crystalline.TwistedScalars` is that two such structures
are in play at once, so neither may be the ambient one. -/
abbrev pointedAlgebra (g : Dt ⟶ X) : Algebra Dt.ring.carrier X.ring.carrier :=
  (pointRingHom (pointedOfHom g)).toAlgebra

/-- **The structure map of `Crystalline.pointedAlgebra` is the chosen map.** -/
@[simp] theorem pointedAlgebra_algebraMap (g : Dt ⟶ X) (a : Dt.ring.carrier) :
    @algebraMap Dt.ring.carrier X.ring.carrier _ _ (pointedAlgebra g) a = g.hom a := rfl

/-! ### The difference family of two pointings -/

variable {ι : Type uI}

/-- **The family `ξ_{f,g} = f(x_i) - g(x_i)` of the proof of [Stacks, Tag 07JH]**, for two
pointings of one object of the pointed crystalline site and a family `x : ι → D` of coordinates.
It is `Crystalline.SecondDividedPowerMap.diff` for the data of
`Crystalline.pointedDatum`, written without reference to an algebra instance. -/
def pointedDiff (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier) : ι → X.ring.carrier :=
  fun i ↦ f.hom (x i) - g.hom (x i)

/-- The `i`-th entry of `Crystalline.pointedDiff f g x` is `f(x_i) - g(x_i)`. -/
@[simp] theorem pointedDiff_apply (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier) (i : ι) :
    pointedDiff f g x i = f.hom (x i) - g.hom (x i) := rfl

/-- **The differences lie in the divided power ideal of `B`**, which is what makes them admit
divided powers and so the Taylor coefficients `ξ^{[K]}` exist.  This is
`Crystalline.sub_pointRingHom_mem_ideal`, the source's "the image of `f - g` is contained in
`J_B`". -/
theorem pointedDiff_mem (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X)
    (x : ι → Dt.ring.carrier) (i : ι) : pointedDiff f g x i ∈ X.ring.ideal :=
  sub_pointRingHom_mem_ideal hDt f g (x i)

/-- The difference family of a pointing with itself vanishes, so `c_{f,f}` has only its
degree-zero term; compare `Crystalline.pointedComparison_self`. -/
@[simp] theorem pointedDiff_self (f : Dt ⟶ X) (x : ι → Dt.ring.carrier) :
    pointedDiff f f x = 0 := by
  funext i
  simp

/-- **The difference families of three pointings add up**: `ξ_{f,g} + ξ_{g,h} = ξ_{f,h}`.  This is
the coefficient identity the cocycle of [Stacks, Tag 07JH] runs on, and it is why the composite of
the series of `ξ_{f,g}` and of `ξ_{g,h}` is the series of `ξ_{f,h}`. -/
theorem pointedDiff_add_pointedDiff (f g h : Dt ⟶ X) (x : ι → Dt.ring.carrier) :
    pointedDiff f g x + pointedDiff g h x = pointedDiff f h x := by
  funext i
  simp only [Pi.add_apply, pointedDiff_apply]
  ring

/-- **Two pointings of one object, as the second divided power map of the second one's instance.**
The datum `Crystalline.SecondDividedPowerMap` is relative to an `Algebra D B`, and at
`Crystalline.pointedAlgebra g` it asks exactly that `f` agree with `g` modulo the divided power
ideal of `B`, which `Crystalline.sub_pointRingHom_mem_ideal` supplies.

So the pair `(f, g)` of pointings is the datum of the Taylor theory with no further
hypothesis than the one making the fixed object crystalline.  Compare
`Crystalline.secondDividedPowerMapOfPointings`, which is this for an ambient instance carrying
`g` only propositionally. -/
def pointedDatum (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X) :
    @SecondDividedPowerMap Dt.ring X.ring (pointedAlgebra g) :=
  letI := pointedAlgebra g
  { hom := f.hom
    sub_algebraMap_mem := fun a ↦ sub_pointRingHom_mem_ideal hDt f g a }

/-- The semilinearity map of the datum of two pointings is the chosen map of the first, so the
semilinear map the Taylor theory produces is semilinear for `f` in the sense of
`Crystalline.pointedComparison`. -/
@[simp] theorem pointedDatum_ringHom (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X) :
    @SecondDividedPowerMap.ringHom Dt.ring X.ring (pointedAlgebra g) (pointedDatum hDt f g) =
      pointRingHom (pointedOfHom f) := rfl

/-- **The difference family of the datum is `ξ_{f,g}`.**  A single
`Crystalline.SecondDividedPowerMap` can express only the difference with its own structure map,
and at `Crystalline.pointedAlgebra g` that structure map is `g`; so the family the Taylor theory
quantifies over is the source's, with no second datum needed. -/
@[simp] theorem pointedDatum_diffFamily (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier) :
    @SecondDividedPowerMap.diffFamily Dt.ring X.ring (pointedAlgebra g) ι
      (pointedDatum hDt f g) x = pointedDiff f g x := rfl

end Algebra

/-! ### The Taylor series in the twisted target -/

section Series

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M] (p : ℕ) {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The Taylor series of [Stacks, Tag 07JH] converges to `t` in the twisted target**: the series
`∑_K ξ^{[K]} ⊗ θ_K(m)` converges `p`-adically in `M ⊗_{D,g} B`.

This is `Crystalline.HasTaylorSum` read at `Crystalline.pointedAlgebra g` and nothing else: the
`D`-algebra structure of `Crystalline.TwistedScalars (pointRingHom (pointedOfHom g))` is that
instance, so `Crystalline.pointedSections M (pointedOfHom g)` is the tensor product the existing
predicate speaks about. -/
def HasPointedTaylorSum (g : Dt ⟶ X) (xi : ι → X.ring.carrier) (m : M)
    (t : pointedSections M (pointedOfHom g)) : Prop :=
  @HasTaylorSum p Dt.ring X.ring (pointedAlgebra g) M _ _ ι thetaPow xi m t

/-- **A Taylor series with finitely many nonzero terms converges to their sum**, in the twisted
target.  This is `Crystalline.hasTaylorSum_of_eq_zero` at `Crystalline.pointedAlgebra g`, with the
vanishing of the terms outside `s` supplied in the form the quasi-nilpotence condition (07JE)
gives it. -/
theorem hasPointedTaylorSum_sum (g : Dt ⟶ X) (xi : ι → X.ring.carrier) {N : ℕ}
    (hpB : ((p : X.ring.carrier)) ^ N = 0) (m : M) (s : Finset (ι →₀ ℕ))
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p Dt.ring.carrier M N) :
    HasPointedTaylorSum M p thetaPow g xi m
      (∑ K ∈ s, TwistedScalars.mk (pointRingHom (pointedOfHom g)) (taylorMonomial X.ring xi K)
        ⊗ₜ[Dt.ring.carrier] thetaPow K m) :=
  let := pointedAlgebra g
  hasTaylorSum_of_eq_zero p Dt.ring X.ring M thetaPow xi m s fun K hK ↦
    taylorTerm_eq_zero_of_mem_pPowSmul p Dt.ring X.ring M thetaPow hpB xi (hvanish K hK)

/-- **A pointed Taylor sum is the finite sum of the terms that do not vanish.**  The sum of a
Taylor series is unique, by `Crystalline.hasTaylorSum_unique` from `p^N = 0` in `B`, and
`Crystalline.hasPointedTaylorSum_sum` exhibits one; so a map carrying the series is computed
term by term, which is what the cocycle identity needs.

`hvanish` is the source's own "the sum is finite!", in the form
`Crystalline.finite_thetaPow_notMem_pPowSmul` proves it from (07JE). -/
theorem hasPointedTaylorSum_eq_sum (g : Dt ⟶ X) (xi : ι → X.ring.carrier) {N : ℕ}
    (hpB : ((p : X.ring.carrier)) ^ N = 0) (m : M) (s : Finset (ι →₀ ℕ))
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p Dt.ring.carrier M N)
    {t : pointedSections M (pointedOfHom g)}
    (ht : HasPointedTaylorSum M p thetaPow g xi m t) :
    t = ∑ K ∈ s, TwistedScalars.mk (pointRingHom (pointedOfHom g)) (taylorMonomial X.ring xi K)
      ⊗ₜ[Dt.ring.carrier] thetaPow K m :=
  let := pointedAlgebra g
  hasTaylorSum_unique p Dt.ring X.ring M thetaPow hpB xi m _ _ ht
    (hasPointedTaylorSum_sum M p thetaPow g xi hpB m s hvanish)

/-- **The surviving multi-indices of a Taylor series are bounded by a `Finset.Iic`.**  The set of
`K` with `θ_K(m) ∉ p^N M` is finite, by `Crystalline.finite_thetaPow_notMem_pPowSmul` from the
quasi-nilpotence condition (07JE) of [Stacks, Tag 07JE], and the pointwise supremum of a finite
set of multi-indices is a multi-index; so the series may be summed over a *downward closed* index
set.

That is what `Crystalline.taylorComposite_prod_eq` needs and what
`Crystalline.hasPointedTaylorSum_pointedComparison_comp` asks for: composing two series produces
the pairs `(K', K'')` drawn from the index set, and only a downward closed set contains every
`K' + K''` that matters.  The remark that `Crystalline.finite_thetaPow_notMem_pPowSmul` "bounds by
a `Finset.Iic`" is made in the docstring of `Crystalline.taylorComposite_prod_Iic_eq`; this is
that bound. -/
theorem exists_Iic_thetaPow_mem_pPowSmul [DecidableEq ι] {N : ℕ} {m : M}
    (hfin : {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    ∃ L : ι →₀ ℕ, ∀ K ∉ Finset.Iic L,
      thetaPow K m ∈ pPowSmul p Dt.ring.carrier M N := by
  classical
  refine ⟨hfin.toFinset.sup id, fun K hK ↦ not_not.mp fun hc ↦ hK ?_⟩
  exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) (hfin.mem_toFinset.mpr hc))

end Series

/-! ### Step one: the semilinear Taylor comparison of a pair -/

section StepOne

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M] (p : ℕ) {ι : Type uI} {theta : ι → (M → M)}
  {thetaPow : (ι →₀ ℕ) → (M → M)}
  {delta : ι → (Dt.ring.carrier → Dt.ring.carrier)}
  {deltaPow : (ι →₀ ℕ) → (Dt.ring.carrier → Dt.ring.carrier)}

/-- **Step one of the proof of [Stacks, Proposition 60.17.4, Tag 07JH]: the semilinear Taylor
comparison of a pair exists.**  For two pointings `f, g : Dt ⟶ X` of one object of the pointed
crystalline site there is an `f`-semilinear map

`T : M →ₛₗ[f] M ⊗_{D,g} B`

whose values are the sums of the Taylor series `∑_K ξ_{f,g}^{[K]} ⊗ θ_K(m)`.  This is the map
`Crystalline.pointedComparison` carries, so with it the source's comparison

`c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`,  `1 ⊗ m ↦ ∑_K θ_K(m) ⊗ ∏_i ξ_i^{[k_i]}`

is available; `Crystalline.exists_pointedComparison` is that reading.

The proof is `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` applied at
`Crystalline.pointedAlgebra g`, where the existing predicate already has the twisted target, and
`Crystalline.pointedDatum` for its datum.  Every hypothesis is that theorem's, except `hDt`, which
is what makes `(f, g)` a datum at all.  See the "Hypotheses carried" section of this module. -/
theorem exists_hasPointedTaylorSum (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X)
    (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow)
    (hthAdd : ∀ (i : ι) (y z : M), theta i (y + z) = theta i y + theta i z)
    (hleib : ∀ (i : ι) (a : Dt.ring.carrier) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (htay : ∀ a : Dt.ring.carrier, ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom g) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f g x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom g) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f g x) J = 0)
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    ∃ Tmap : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g),
      ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (Tmap m) :=
  let := pointedAlgebra g
  exists_isTwistedTaylorComparison_of_taylorFormula p hfamM hfamD hthAdd hleib
    (fun i ↦ pointedDiff_mem hDt f g x i) hpB (pointedDatum hDt f g) htay hfin

/-- **The comparison `c_{f,g}` of the proof of [Stacks, Tag 07JH] exists**, as a `B`-linear map

`M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`

sending the generator `1 ⊗ m` to the sum of the Taylor series `∑_K ξ_{f,g}^{[K]} ⊗ θ_K(m)`.  This
is `Crystalline.exists_hasPointedTaylorSum` read through `Crystalline.pointedComparison`, which by
`Crystalline.semilinearBaseChange_unique` is the only `B`-linear map with those values on the
generators.

It is not yet independence of the choice of pointing: that is the cocycle, whose Taylor-level half
is `Crystalline.hasPointedTaylorSum_pointedComparison_comp` and whose map-level half is
`Crystalline.pointedComparison_comp`. -/
theorem exists_pointedComparison (hDt : Function.Surjective Dt.toQuotient) (f g : Dt ⟶ X)
    (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow)
    (hthAdd : ∀ (i : ι) (y z : M), theta i (y + z) = theta i y + theta i z)
    (hleib : ∀ (i : ι) (a : Dt.ring.carrier) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (htay : ∀ a : Dt.ring.carrier, ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom g) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f g x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom g) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f g x) J = 0)
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    ∃ c : pointedSections M (pointedOfHom f) →ₗ[X.ring.carrier]
        pointedSections M (pointedOfHom g),
      ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m
        (c ((1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m)) := by
  obtain ⟨Tmap, hTmap⟩ := exists_hasPointedTaylorSum M p hDt f g x hfamM hfamD hthAdd hleib hpB
    htay hfin
  refine ⟨pointedComparison M f g Tmap, fun m ↦ ?_⟩
  rw [pointedComparison_one_tmul]
  exact hTmap m

/-- **The comparison `c_{f,g}` for two pointings of an object of the site, with the nilpotence of
`p` discharged.**  This is `Crystalline.exists_pointedComparison` at the prime of the situation,
where the hypothesis `hpB` is not an assumption but part of the definition of a divided power
thickening in [Stacks, Tag 07HM]: `Crystalline.DividedPowerThickening.prime_nilpotent` supplies it
for every object of `CRIS(C/A)`.

`hfin` is quantified over the exponent because the exponent is the one the nilpotence produces and
not a choice; it is the form `Crystalline.finite_thetaPow_notMem_pPowSmul` proves from the
quasi-nilpotence condition (07JE) of [Stacks, Tag 07JE], which holds at every level. -/
theorem exists_pointedComparison_of_thickening (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow)
    (hthAdd : ∀ (i : ι) (y z : M), theta i (y + z) = theta i y + theta i z)
    (hleib : ∀ (i : ι) (a : Dt.ring.carrier) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    (htay : ∀ a : Dt.ring.carrier, ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom g) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f g x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom g) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f g x) J = 0)
    (hfin : ∀ (N : ℕ) (m : M),
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul S.p Dt.ring.carrier M N}.Finite) :
    ∃ c : pointedSections M (pointedOfHom f) →ₗ[X.ring.carrier]
        pointedSections M (pointedOfHom g),
      ∀ m : M, HasPointedTaylorSum M S.p thetaPow g (pointedDiff f g x) m
        (c ((1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m)) := by
  obtain ⟨N, hN⟩ := X.prime_nilpotent
  exact exists_pointedComparison M S.p hDt f g x hfamM hfamD hthAdd hleib hN htay (hfin N)

end StepOne

/-! ### Step two: the cocycle at the level of the Taylor series -/

section StepTwo

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M] (p : ℕ) {ι : Type uI} [DecidableEq ι] {theta : ι → (M → M)}
  {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **Step two of the proof of [Stacks, Proposition 60.17.4, Tag 07JH]: the composite of two
comparisons carries the Taylor series of the third family.**  If `T₁` carries the series of
`ξ_{f,g}` and `T₂` that of `ξ_{g,h}`, then `c_{g,h} ∘ T₁` carries the series of `ξ_{f,h}`.

Together with `Crystalline.pointedComparison_comp`, which says
`c_{g,h} ∘ c_{f,g} = c_{f,h}` for the composed semilinear map, this is the source's "A computation
shows that `c_{g,h} ∘ c_{f,g} = c_{f,h}`" with both sides identified as comparisons of the
families the tag names: the composite is not merely *a* comparison but the comparison of
`ξ_{f,h}`.

The proof is the cocycle `Crystalline.taylorComposite_prod_eq` read at
`Crystalline.pointedAlgebra h`, where the terms of the composite live.  `T₁ m` and the `T₂`'s are
replaced by their finite sums by `Crystalline.hasPointedTaylorSum_eq_sum`, the two sums are
multiplied out, and the coefficient families add up by
`Crystalline.pointedDiff_add_pointedDiff`.

The index set is a `Finset.Iic`, which is what makes `Crystalline.taylorComposite_prod_eq`
applicable: that theorem needs its index set downward closed, and
`Crystalline.finite_thetaPow_notMem_pPowSmul` bounds the nonvanishing multi-indices by such a
set. -/
theorem hasPointedTaylorSum_pointedComparison_comp
    (hDt : Function.Surjective Dt.toQuotient) (f g h : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom h))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow h (pointedDiff g h x) m (T₂ m))
    (m : M) (L : ι →₀ ℕ)
    (hvanish : ∀ K ∉ Finset.Iic L, thetaPow K m ∈ pPowSmul p Dt.ring.carrier M N) :
    HasPointedTaylorSum M p thetaPow h (pointedDiff f h x) m
      (pointedComparison M g h T₂ (T₁ m)) := by
  classical
  let := pointedAlgebra h
  set s : Finset (ι →₀ ℕ) := Finset.Iic L with hs
  set xi : ι → X.ring.carrier := pointedDiff f g x with hxi
  set eta : ι → X.ring.carrier := pointedDiff g h x with heta
  -- The series of `T₁` is its finite sum over `s`.
  have hT1eq : T₁ m = ∑ K ∈ s,
      TwistedScalars.mk (pointRingHom (pointedOfHom g)) (taylorMonomial X.ring xi K)
        ⊗ₜ[Dt.ring.carrier] thetaPow K m :=
    hasPointedTaylorSum_eq_sum M p thetaPow g xi hpB m s hvanish (hT₁ m)
  -- The series of `T₂` at each `θ_{K'} m` is its finite sum over the same `s`.
  have hT2eq : ∀ K' ∈ s, T₂ (thetaPow K' m) = ∑ K'' ∈ s,
      TwistedScalars.mk (pointRingHom (pointedOfHom h)) (taylorMonomial X.ring eta K'')
        ⊗ₜ[Dt.ring.carrier] thetaPow K'' (thetaPow K' m) := by
    intro K' _
    refine hasPointedTaylorSum_eq_sum M p thetaPow h eta hpB _ s (fun K hK ↦ ?_) (hT₂ _)
    have hcomp : thetaPow K (thetaPow K' m) = thetaPow (K' + K) m := (hfamM.add K' K ▸ rfl)
    rw [hcomp]
    refine hvanish _ fun hmem ↦ hK ?_
    exact Finset.mem_Iic.mpr (le_add_self.trans (Finset.mem_Iic.mp hmem))
  -- Expand the composite term by term.
  have hexpand : pointedComparison M g h T₂ (T₁ m) =
      ∑ K' ∈ s, ∑ K'' ∈ s,
        TwistedScalars.mk (pointRingHom (pointedOfHom h))
            (taylorMonomial X.ring xi K' * taylorMonomial X.ring eta K'')
          ⊗ₜ[Dt.ring.carrier] thetaPow K'' (thetaPow K' m) := by
    rw [hT1eq, map_sum]
    refine Finset.sum_congr rfl fun K' hK' ↦ ?_
    rw [pointedComparison, semilinearBaseChange_tmul, hT2eq K' hK', Finset.smul_sum]
    refine Finset.sum_congr rfl fun K'' _ ↦ ?_
    rw [TensorProduct.smul_tmul']
    rfl
  have hcocycle := taylorComposite_prod_Iic_eq (p := p) (B := X.ring) (M := M)
    (thetaPow := thetaPow) hfamM (xi := xi) (eta := eta)
    (fun i ↦ pointedDiff_mem hDt f g x i) (fun i ↦ pointedDiff_mem hDt g h x i) hpB m L hvanish
  rw [hexpand, ← pointedDiff_add_pointedDiff f g h x]
  refine Eq.mpr (congrArg (HasPointedTaylorSum M p thetaPow h _ m) hcocycle) ?_
  exact hasPointedTaylorSum_sum M p thetaPow h _ hpB m s hvanish

omit [DecidableEq ι] in
/-- **The cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}` of the proof of [Stacks, Proposition 60.17.4,
Tag 07JH], as an identity between the comparisons of the tag's own families.**

`Crystalline.pointedComparison_comp` says the composite of two comparisons is the comparison of
the composed semilinear map, which leaves open which family that map carries;
`Crystalline.hasPointedTaylorSum_pointedComparison_comp` says it carries the series of `ξ_{f,h}`;
and the sum of a Taylor series is unique.  Put together: any `T₃` carrying the series of
`ξ_{f,h}` has `c_{f,h} = c_{g,h} ∘ c_{f,g}`.

This is the source's "A computation shows that `c_{g,h} ∘ c_{f,g} = c_{f,h}`" in full, and not the
weaker statement that the composite is *some* comparison.  The remaining hypothesis `hfin` is the
source's own "the sum is finite!", which `Crystalline.exists_Iic_thetaPow_mem_pPowSmul` turns into
the downward closed index set the computation runs over.

What this does not give by itself is independence of the choice of pointing on the *unpointed*
site: that needs the comparisons to be isomorphisms, for which `c_{f,f} = 1`
(`Crystalline.pointedComparison_self`) and this identity are the two inputs, and the descent along
the forgetful functor, which consumes both and is
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedDescent.lean`. -/
theorem pointedComparison_comp_eq (hDt : Function.Surjective Dt.toQuotient) (f g h : Dt ⟶ X)
    (x : ι → Dt.ring.carrier) (hfamM : IsThetaMonomialFamily M theta thetaPow)
    {N : ℕ} (hpB : ((p : X.ring.carrier)) ^ N = 0)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom h))
    (T₃ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom h))
    (hT₁ : ∀ m : M, HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m (T₁ m))
    (hT₂ : ∀ m : M, HasPointedTaylorSum M p thetaPow h (pointedDiff g h x) m (T₂ m))
    (hT₃ : ∀ m : M, HasPointedTaylorSum M p thetaPow h (pointedDiff f h x) m (T₃ m))
    (hfin : ∀ m : M,
      {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p Dt.ring.carrier M N}.Finite) :
    (pointedComparison M g h T₂).comp (pointedComparison M f g T₁) =
      pointedComparison M f h T₃ := by
  classical
  have key : ∀ m : M, pointedComparison M g h T₂ (T₁ m) = T₃ m := by
    intro m
    obtain ⟨L, hL⟩ := exists_Iic_thetaPow_mem_pPowSmul M p thetaPow (hfin m)
    let := pointedAlgebra h
    exact hasTaylorSum_unique p Dt.ring X.ring M thetaPow hpB (pointedDiff f h x) m _ _
      (hasPointedTaylorSum_pointedComparison_comp M p hDt f g h x hfamM hpB T₁ T₂ hT₁ hT₂ m L hL)
      (hT₃ m)
  rw [pointedComparison_comp]
  exact congrArg (pointedComparison M f h) (LinearMap.ext key)

end StepTwo

/-! ### The hypotheses are satisfiable -/

section Satisfiable

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X : DividedPowerThickening.{u, v, w} S} {ι : Type uI}
  {delta : ι → (Dt.ring.carrier → Dt.ring.carrier)}
  {deltaPow : (ι →₀ ℕ) → (Dt.ring.carrier → Dt.ring.carrier)}

/-- **Taylor's formula in `B` holds at one pointing**, where the coordinate differences vanish and
the series has only its degree-zero term, which is `f(a)` itself.

So the hypothesis `htay` of `Crystalline.exists_hasPointedTaylorSum` is satisfiable and that
theorem is not the empty statement.  Compare `Crystalline.taylorFormula_refl`, which is this for
the degenerate datum of `Crystalline.SecondDividedPowerMap.refl`; stating it for a pointing is
what makes `Crystalline.exists_hasPointedTaylorSum` inhabited at `g = f`, where its conclusion is
`Crystalline.pointedUnitComparison` and `Crystalline.pointedComparison_self` identifies the
comparison with the identity. -/
theorem taylorFormula_pointed_self (f : Dt ⟶ X) (x : ι → Dt.ring.carrier)
    (hfamD : IsThetaMonomialFamily Dt.ring.carrier delta deltaPow) (a : Dt.ring.carrier) :
    ∃ t : Finset (ι →₀ ℕ),
      (pointRingHom (pointedOfHom f) a = ∑ J ∈ t,
          pointRingHom (pointedOfHom f) (deltaPow J a) *
            taylorMonomial X.ring (pointedDiff f f x) J) ∧
        ∀ J ∉ t, pointRingHom (pointedOfHom f) (deltaPow J a) *
          taylorMonomial X.ring (pointedDiff f f x) J = 0 := by
  classical
  refine ⟨{0}, ?_, fun J hJ ↦ ?_⟩
  · rw [Finset.sum_singleton, taylorMonomial_zero, mul_one, hfamD.apply_zero]
    rfl
  · rw [pointedDiff_self, taylorMonomial_zero_family X.ring (by simpa using hJ), mul_zero]

end Satisfiable

end Crystalline

end
