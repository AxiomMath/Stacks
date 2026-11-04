module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFreeFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCrystal07JG
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily

/-!
# An algebraic model of [Stacks, Proposition 60.17.4, Tag 07JH]

[Stacks, Proposition 60.17.4, Tag 07JH] says that the functor of [Stacks, Lemma 60.17.3,
Tag 07JG], from the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the pairs
`(M, ∇)` satisfying its four items (07JB), (07JC), (07JD) and (07JE), is an **equivalence of
categories**.  The functor of Tag 07JG in the affine algebraic form of this chapter is
`Crystalline.taylorCrystalsToPairs`, which is where `@[stacks 07JG]` sits; this module proves that
that functor is an equivalence, which is this tag for it.

## The quasi-inverse, link by link

The functor factors as

`Crystalline.forgetToFirstOrderCrystal ⋙ Crystalline.firstOrderCrystalsToPairs`

and each factor is an equivalence.

**The second factor.**  `Crystalline.firstOrderCrystalsToPairs` goes from the first-order
comparison data over `D` to the pairs.  Faithfulness is
`Crystalline.firstOrderCrystalsToPairs_faithful`.  Fullness is
`Crystalline.firstOrderCrystalsToPairs_full_of_injective`, which asks that the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω` be injective; a basis of `Ω` gives that, by
`Crystalline.forall_injective_toCompletedTensor_of_basis`.  Essential surjectivity is
`Crystalline.firstOrderCrystalsToPairs_essSurj_of_exists_lift`, which asks that the connection of
a pair factor through `M ⊗_D Ω`; a basis with a **finite** index type gives that, by
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis`, and
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` shows the finiteness cannot be
dropped from that route.

**The first factor**, which is what this module adds.
`Crystalline.forgetToFirstOrderCrystal` forgets the tower of levels `M_e` and the composite
coordinate operators `θ_K` and keeps the four items they prove.  It is full and faithful on the
nose, the morphisms of its source being by definition those of the images.  What this module proves is
that it is **essentially surjective**: that the tower and the operators can be rebuilt from the
four items, which is exactly what the proof of the tag has to do when it runs the construction of
Tag 07JG backwards out of a pair.  Both are rebuilt in
`StacksFrontier/AlgebraicGeometry/Crystalline/ThetaMonomialFamily.lean`:

* the tower is `M_e = M ⧸ p^e M` with the quotient maps, and the identification `M ≅ lim_e M_e`
  is `Crystalline.adicLevelLimitEquiv`, from item (07JB) alone — the level `e` is annihilated by
  `p^e` by `Crystalline.pLevel_quotient_eq_bot`, so the shift of
  `Crystalline.TaylorCrystal.level_annihilate` is `0` here;
* the composite operators are `Crystalline.exists_isThetaMonomialFamily` applied to a family of
  coordinate operators of the connection, which exists by the non-vacuity clause
  `Crystalline.Pair.hasCoordinateOperators` and commutes by item (07JD);
* the convergence clause `Crystalline.TaylorCrystal.finite_thetaPow_notMem_pSmul` is item (07JE),
  through `Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent`, whose
  additivity input is `Crystalline.map_add_of_isCoordinateExpansion`.

So no item of the pair is used twice and none is strengthened: the three data of
`Crystalline.TaylorCrystal` beyond the comparison datum are recovered from the four items, which
is the content of "quasi-inverse" for this factor.

## Main results

* `Crystalline.FirstOrderCrystal.toTaylorCrystal` — **the lift of a first-order crystal datum to
  a `Crystalline.TaylorCrystal`**, the object half of the quasi-inverse of the first factor.
* `Crystalline.forgetToFirstOrderCrystal_faithful`,
  `Crystalline.forgetToFirstOrderCrystal_full`,
  `Crystalline.forgetToFirstOrderCrystal_essSurj` and
  `Crystalline.forgetToFirstOrderCrystal_isEquivalence` — the first factor is an equivalence.
* `Crystalline.taylorCrystalsToPairs_isEquivalence` — the equivalence of categories of
  [Stacks, Proposition 60.17.4, Tag 07JH] **for `Crystalline.taylorCrystalsToPairs`, whose source
  is the affine algebraic model `Crystalline.TaylorCrystal` and not the crystals in
  quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` that the tag goes out of**, and with the index
  type of the coordinates finite, which the tag does not ask for.  Both discrepancies are set out
  below and in the theorem's own docstring.

## What the source omits, and what is proved instead

The source's proof of the tag goes through the unpointed site: it picks, for each affine object
`(U, T, δ)` of `Cris(X/S)`, a map `f : D → B` and sets `ℱ_T = M ⊗_{D,f} B`, compares two choices
by the Taylor isomorphism `c_{f,g}`, and then says three times that a verification is omitted —
independence of the restriction maps from the choice of `f`, the extension of the crystal from the
affine objects to all of `Cris(X/S)`, and that the procedure is a functor quasi-inverse to the one
of Tag 07JG.  The route taken here does not need any of the three, because it does not descend
along the choice of `f` at all: the equivalence is proved for the functor of Tag 07JG itself by
exhibiting the quasi-inverse on the two factors through which that functor is built, and the only
Taylor expansion that enters is the one in degrees `∑ k_i ≤ 1`, which is
`Crystalline.FirstOrderComparison.ofConnection`.  The higher degrees, the divided power
coefficients `∏ ξ_i^{[k_i]}` and the cocycle identity are the subject of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorFormulaMonomials.lean`,
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorConvergence.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean`; they are what the source's own
route needs and this one does not.  All three of the source's omitted verifications are now
discharged on that route — independence of the restriction maps from the choice of `f` is
`Crystalline.pointedRestriction_pointedComparison`, the crystal condition is
`Crystalline.existsUnique_pointedRestriction`, and the descent of the whole assignment to the
unpointed algebraic site, with its functoriality in the object and in the pair, is
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedDescent.lean`.  What that route still lacks is
the passage to quasi-coherent sheaves on `Cris(X/S)` and the functor of Tag 07JG out of that
source category.

The index type of the coordinates is finite, and that **is** an extra condition: the source
imposes no finiteness anywhere.  It is not a reading of the hypotheses of Tag 07JG, even though
`Crystalline.TaylorCrystal` asks for a `Module.Basis ι D Ω` on the differentials `d x_i` and the
`Ω_D` of [Stacks, Tag 07J9] — the `p`-adic completion of the free module on the `d x_i` — has the
differentials for an algebraic basis exactly when the coordinates are finitely many.  What this
shows is that the *model* carries the condition, not that the tag does: with infinitely many coordinates the source's own
`∑ f_i d x_i` is a convergent series rather than a finite combination, so `Ω_D` is not free and
`Crystalline.TaylorCrystal` — whose comparison datum is valued in the **uncompleted**
`(D ⊕ Ω) ⊗_D M` — is not the right model of the pair there.

The finiteness is in consequence not removable on this route: essential surjectivity of `Crystalline.firstOrderCrystalsToPairs` runs on the
factorisation of the connection of a pair through the uncompleted `M ⊗_D Ω`, and
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean` shows that `ℕ →₀ R` is
not `p`-adically precomplete when no power of `p` vanishes — which is the `D` at hand.  A
finiteness-free statement has to avoid the first-order datum altogether, as the source's own proof
does: it uses the full Taylor series in all divided power degrees.  That route is the one whose
descent from the pointed site is
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedDescent.lean`, where no finiteness of the index
type enters.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open CategoryTheory

universe u uI

namespace Crystalline

/-! ### The data of a `Crystalline.TaylorCrystal` rebuilt from the four items -/

namespace FirstOrderCrystal

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  (Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx)

/-- **A family of coordinate operators of the connection of `Q`**, chosen once and for all.  Its
existence is the non-vacuity clause `hasCoordinateOperators`, and by
`Crystalline.eq_of_isCoordinateExpansion` the choice is in fact unique, so nothing depends on
it. -/
noncomputable def chosenTheta : ι → (Q.carrier → Q.carrier) :=
  Q.hasCoordinateOperators.choose

/-- The chosen operators expand the connection: `∇ m = ∑_i θ_i(m) d x_i`. -/
theorem chosenTheta_isCoordinateExpansion :
    IsCoordinateExpansion p D Omega dx (Q.comparison.completedConnection p) Q.chosenTheta :=
  Q.hasCoordinateOperators.choose_spec

/-- **The chosen operators commute**, which is item (07JD), integrability. -/
theorem chosenTheta_comm (i j : ι) :
    Q.chosenTheta i ∘ Q.chosenTheta j = Q.chosenTheta j ∘ Q.chosenTheta i :=
  Q.isIntegrable _ Q.chosenTheta_isCoordinateExpansion i j

/-- **The composite operators `θ_K = ∏_i θ_i^{k_i}` of the chosen family.**  They exist because
the chosen operators commute, by `Crystalline.exists_isThetaMonomialFamily`. -/
noncomputable def chosenThetaPow : (ι →₀ ℕ) → (Q.carrier → Q.carrier) :=
  (exists_isThetaMonomialFamily Q.chosenTheta Q.chosenTheta_comm).choose

/-- `θ_K = ∏_i θ_i^{k_i}` for the chosen families. -/
theorem chosenThetaPow_isThetaMonomialFamily :
    IsThetaMonomialFamily Q.carrier Q.chosenTheta Q.chosenThetaPow :=
  (exists_isThetaMonomialFamily Q.chosenTheta Q.chosenTheta_comm).choose_spec

/-- **The chosen operators are additive**, by `Crystalline.map_add_of_isCoordinateExpansion`:
uniqueness of the coordinate expansion turns additivity of `∇` into additivity of the `θ_i`. -/
theorem chosenTheta_map_add (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i)
    (i : ι) (x y : Q.carrier) :
    Q.chosenTheta i (x + y) = Q.chosenTheta i x + Q.chosenTheta i y := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Q.carrier :=
    Q.isPAdicallyComplete
  exact map_add_of_isCoordinateExpansion p (D : Type u) Omega Q.carrier
    Q.chosenTheta_isCoordinateExpansion b hdx IsAdicComplete.toIsHausdorff i x y

/-- **The convergence clause of `Crystalline.TaylorCrystal` for the chosen families**: for every
`m` only finitely many multi-indices `K` have `θ_K(m) ∉ p M`.  This is item (07JE), topological
quasi-nilpotence, read on the monomial family by
`Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent`. -/
theorem finite_chosenThetaPow_notMem_pSmul (b : Module.Basis ι (D : Type u) Omega)
    (hdx : ∀ i, dx i = b i) (m : Q.carrier) :
    {K : ι →₀ ℕ | Q.chosenThetaPow K m ∉ pSmul p (D : Type u) Q.carrier}.Finite :=
  finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent p (D : Type u) Omega Q.carrier
    Q.chosenThetaPow_isThetaMonomialFamily (Q.chosenTheta_map_add b hdx)
    Q.chosenTheta_isCoordinateExpansion b hdx Q.isTopologicallyQuasiNilpotent m

/-- **The lift of a first-order crystal datum to a `Crystalline.TaylorCrystal`.**

This is the object half of the quasi-inverse of `Crystalline.forgetToFirstOrderCrystal`: the three
data that `Crystalline.TaylorCrystal` carries beyond the comparison datum are rebuilt from the
four items of the datum, with the same module and the same comparison map.

* The tower is `M_e = M ⧸ p^e M` with the quotient maps; the level `e` is annihilated by `p^e`
  by `Crystalline.pLevel_quotient_eq_bot`, so the exponent shift is `0`, and the identification
  `M ≅ lim_e M_e` is `Crystalline.adicLevelLimitEquiv` applied to item (07JB).
* The coordinate operators are `Crystalline.FirstOrderCrystal.chosenTheta` and their composites
  `Crystalline.FirstOrderCrystal.chosenThetaPow`.
* The convergence clause is item (07JE), by
  `Crystalline.FirstOrderCrystal.finite_chosenThetaPow_notMem_pSmul`. -/
noncomputable def toTaylorCrystal (b : Module.Basis ι (D : Type u) Omega)
    (hdx : ∀ i, dx i = b i) : TaylorCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx where
  carrier := Q.carrier
  comparison := Q.comparison
  levels := adicLevel (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Q.carrier
  transition := adicLevelTransition (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Q.carrier
  shift := 0
  level_annihilate n := by
    rw [zero_add]
    exact pLevel_quotient_eq_bot p (D : Type u) Q.carrier n
  levelEquiv := adicLevelLimitEquiv _ Q.carrier Q.isPAdicallyComplete
  theta := Q.chosenTheta
  thetaPow := Q.chosenThetaPow
  isThetaMonomialFamily := Q.chosenThetaPow_isThetaMonomialFamily
  isCoordinateExpansion := Q.chosenTheta_isCoordinateExpansion
  finite_thetaPow_notMem_pSmul := Q.finite_chosenThetaPow_notMem_pSmul b hdx

/-- The lift has the first-order crystal datum it was built from: the module and the comparison
map are unchanged, and the four items are propositions. -/
@[simp] theorem toTaylorCrystal_toFirstOrderCrystal (b : Module.Basis ι (D : Type u) Omega)
    (hdx : ∀ i, dx i = b i) : (Q.toTaylorCrystal b hdx).toFirstOrderCrystal = Q := rfl

end FirstOrderCrystal

/-! ### The forgetful functor is an equivalence -/

section Forget

variable (A : Type u) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u)
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
  (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i)

/-- **`Crystalline.forgetToFirstOrderCrystal` is faithful**, on the nose: a morphism of
`Crystalline.TaylorCrystal` *is* a morphism of the images. -/
theorem forgetToFirstOrderCrystal_faithful :
    Functor.Faithful (forgetToFirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx) where
  map_injective h := h

/-- **`Crystalline.forgetToFirstOrderCrystal` is full**, on the nose, for the same reason. -/
theorem forgetToFirstOrderCrystal_full :
    Functor.Full (forgetToFirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx) where
  map_surjective f := ⟨f, rfl⟩

/-- **`Crystalline.forgetToFirstOrderCrystal` is essentially surjective**: the tower of levels and
the composite coordinate operators that `Crystalline.TaylorCrystal` carries are recovered from the
four items of a first-order crystal datum, by
`Crystalline.FirstOrderCrystal.toTaylorCrystal`.

This is the half of the quasi-inverse of [Stacks, Tag 07JH] that the source's proof performs when
it reads the operators `θ_K` off a pair `(M, ∇)` and rebuilds the modules over the objects `T_e`;
here it is an identity of objects rather than an isomorphism, because the lift changes neither the
module nor the comparison map. -/
theorem forgetToFirstOrderCrystal_essSurj :
    Functor.EssSurj (forgetToFirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx) where
  mem_essImage Q :=
    ⟨Q.toTaylorCrystal b hdx, ⟨eqToIso (Q.toTaylorCrystal_toFirstOrderCrystal b hdx)⟩⟩

/-- **`Crystalline.forgetToFirstOrderCrystal` is an equivalence of categories.** -/
theorem forgetToFirstOrderCrystal_isEquivalence :
    Functor.IsEquivalence
      (forgetToFirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx) where
  faithful := forgetToFirstOrderCrystal_faithful A D g Omega d p dx b hdx
  full := forgetToFirstOrderCrystal_full A D g Omega d p dx b hdx
  essSurj := forgetToFirstOrderCrystal_essSurj A D g Omega d p dx b hdx

end Forget

/-! ### The tag -/

section Tag

variable (A : Type u) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u)
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} [Finite ι] (dx : ι → Omega)

/-- **The second factor `Crystalline.firstOrderCrystalsToPairs` is an equivalence of
categories.**  Its two hypotheses are supplied by the basis of `Ω`: injectivity of
`M ⊗_D Ω → M ⊗̂_D Ω` by `Crystalline.forall_injective_toCompletedTensor_of_basis`, which needs no
finiteness, and the factorisation of the connection of a pair through `M ⊗_D Ω` by
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis`, which does. -/
theorem firstOrderCrystalsToPairs_isEquivalence_of_finite_basis
    (b : Module.Basis ι (D : Type u) Omega) :
    Functor.IsEquivalence
      (firstOrderCrystalsToPairs.{u, u, u, uI, u} A D g Omega d p dx) :=
  firstOrderCrystalsToPairs_isEquivalence A D g Omega d p dx
    (forall_injective_toCompletedTensor_of_basis p dx b)
    (forall_exists_firstOrderConnection_of_finite_basis A D g Omega d p dx b)

/-- **The algebraic model of [Stacks, Proposition 60.17.4, Tag 07JH]**, which carries no
`@[stacks 07JH]` attribute: the tag is about the crystals in quasi-coherent modules on `Cris(X/S)`
(`Crystalline.GlobalCrystallineSituation.SmallSite.QuasiCoherentCrystal`), not about this model.
The functor of [Stacks, Lemma 60.17.3, Tag 07JG] — `Crystalline.taylorCrystalsToPairs`, the
declaration this chapter registers that lemma on — from `Crystalline.TaylorCrystal` to the pairs
`(M, ∇)` satisfying items (07JB), (07JC), (07JD) and (07JE), with its canonical crystalline
connection, **is an equivalence of categories.**

**The source category is `Crystalline.TaylorCrystal` and not the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`.**  It is the affine algebraic model over `D` of the data a
crystal supplies: a `D`-module with a first-order comparison datum, a tower of levels realising
it as `lim_e M_e`, and the composite coordinate operators of the expansion over `D(1)`.  The
corresponding statement for the tag's own source is
`Crystalline.GlobalCrystallineSituation.SmallSite.Equivalence07JH` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean`, a `Prop` with no
theorem behind it, and the module documentation of that file lists what separates the two.

The functor is `Crystalline.forgetToFirstOrderCrystal ⋙
Crystalline.firstOrderCrystalsToPairs` by definition, and each factor is an equivalence:
`Crystalline.forgetToFirstOrderCrystal_isEquivalence`, whose essential surjectivity rebuilds the
tower of levels from item (07JB) and the composite coordinate operators `θ_K = ∏_i θ_i^{k_i}` from
item (07JD); and `Crystalline.firstOrderCrystalsToPairs_isEquivalence_of_finite_basis`, whose
quasi-inverse is the first-order Taylor comparison `ε m = 1 ⊗ m + ι(∇ m)` of
`Crystalline.FirstOrderComparison.ofConnection`.

The setting is that of the Tag 07JG registration — the base ring, the divided power ring `D` with
its derivation to `Ω`, the prime `p`, the differentials `d x_i` and a `Module.Basis` of `Ω` on
them — with the index type of the coordinates finite, as it is for the `Ω_D` of
[Stacks, Tag 07J9] of a presentation with finitely many variables.  The source states no
finiteness, and the hypothesis is not removable here: the factorisation of the connection of a
pair through `M ⊗_D Ω` that the quasi-inverse runs on fails on an infinite basis, by
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis` and the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`. -/
theorem taylorCrystalsToPairs_isEquivalence (b : Module.Basis ι (D : Type u) Omega)
    (hdx : ∀ i, dx i = b i) :
    Functor.IsEquivalence
      (taylorCrystalsToPairs.{u, u, u, uI, u} A D g Omega d p dx b hdx) := by
  have := forgetToFirstOrderCrystal_isEquivalence A D g Omega d p dx b hdx
  have := firstOrderCrystalsToPairs_isEquivalence_of_finite_basis A D g Omega d p dx b
  exact inferInstanceAs (Functor.IsEquivalence
    (forgetToFirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx b hdx ⋙
      firstOrderCrystalsToPairs.{u, u, u, uI, u} A D g Omega d p dx))

end Tag

end Crystalline

end
