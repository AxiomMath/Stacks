module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPolynomialDecomposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareHomotopy

/-!
# The relative divided power Poincaré lemma over the `p`-adic completion

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.  Write `D` for the `p`-adic
completion of `B`, `D'` for the `p`-adic completion of `P`, and `Ω̂^*_D`, `Ω̂^*_{D'}` for the
`p`-adic completions of the divided power de Rham complexes, as built in
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDividedPowerForms.lean`.  This module proves
the **completed clause** of [Stacks, Lemma 60.19.2, Tag 07LD] for `P`:

`d (ĥ x) + ĥ (d x) = x - ψ̂ (ε̂ x)`,   `ε̂ ∘ ψ̂ = id`,

so the comparison `ψ̂ : Ω̂^*_D → Ω̂^*_{D'}` of completed de Rham complexes is a homotopy
equivalence with retraction `ε̂`.

`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareHomotopy.lean` proves the
uncompleted identity `d (h x) + h (d x) = x - ψ (ε x)` on `Ω^*_{P/A,δ'}`, with the divided power
ideal `I` of the base arbitrary and with `W` an arbitrary family.  This module carries that
identity across the `p`-adic completion.

## Why this is about the completion and not about the levels

The statement below is a single identity between maps *of the completions* `Ω̂^n_{D'}`, not a
family of identities at the levels `p^n` with the limit left implicit.  Deducing a statement about
`D'` from a statement at each level is in general impossible — a quasi-isomorphism at every level
`p^n` does not give one for the limit, since the inverse limit is not exact — and nothing of that
kind is done here.  What makes the transfer legitimate is that a *contraction* is an identity
between maps, and every map in it is the `p`-adic completion of its uncompleted counterpart:

* `Crystalline.PAdicCompletion.mapAddHom` is a functor on **additive** maps, by
  `Crystalline.PAdicCompletion.mapAddHom_comp`, `..._add`, `..._id`, because the level
  `(p)^k · Ω^n` is the subgroup `p^k Ω^n` cut out by an integer;
* `Crystalline.completedDividedPowerDeRham` is, by construction, that functor applied to the
  uncompleted de Rham differential — it is *not* `AdicCompletion.map` of anything, the de Rham
  differential being `A`-linear and not `P`-linear;
* so is the completed homotopy, and so, by
  `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMap_toAddMonoidHom`, is the
  library's completed comparison `Crystalline.completedMapDifferentialForms` of forms.

Applying one additive functor to one identity of maps is therefore the whole proof, and it is also
the source's own argument: the homotopy of the uncompleted complex respects the `p`-adic
filtration, hence completes.  No ext principle over the completed decomposition
`Crystalline.DividedPowerPolynomial.completedDividedPowerPolynomialFormsEquiv` is needed, and
none is used; that decomposition is imported only so that the completed forms here are literally
the object it splits.

## What is and is not claimed

`ψ̂` and `ε̂` are a homotopy equivalence in the full sense: `ψ̂` is a map of complexes by
`Crystalline.completedMapDifferentialForms_deRham`, `ε̂` is one by
`..._completedRelativeFormsRetraction_completedDividedPowerDeRham` in the namespace
`Crystalline.DividedPowerPolynomial`,
`ε̂ ∘ ψ̂ = id`, and `ψ̂ ∘ ε̂` is homotopic to the identity by the contraction.  That `ε̂` is a map
of complexes is not an extra input but a consequence: `ψ̂` is injective, so `ε̂ (d x) = d (ε̂ x)`
may be checked after applying `ψ̂`, and there the contraction computes both sides.

The source's clause asserts that `M ⊗̂_D Ω^*_D → M ⊗̂_D Ω^*_{D'}` is a quasi-isomorphism for a
`p`-adically complete `D`-module `M` with a completed connection.  What this module proves is the
case `M = D`, the geometric content, and as a homotopy equivalence rather than merely as a
quasi-isomorphism; the module is put back in by
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, which perturbs the `ĥ` below against
the connection and needs from it the three side conditions of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareSpecial.lean`.  The base's
divided power ideal `I` stays arbitrary and `W` stays an arbitrary family of variables, exactly as
in the uncompleted identity.

## Main definitions

* `Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy` — **the completed
  contracting homotopy `ĥ : Ω̂^{n+1}_{D'} → Ω̂^n_{D'}`.**
* `Crystalline.DividedPowerPolynomial.completedRelativeFormsRetraction` — **the completed
  coefficient retraction `ε̂ : Ω̂^n_{D'} → Ω̂^n_D`.**
* `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMap` — the completed comparison
  `ψ̂ : Ω̂^n_D → Ω̂^n_{D'}`, which is the library's `Crystalline.completedMapDifferentialForms`
  along the coefficient inclusion `B → P`.
* `Crystalline.DividedPowerPolynomial.completedRelativeFormsProjection` — `ψ̂ ∘ ε̂`.

## Main results

* `Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` —
  **`d (ĥ x) + ĥ (d x) = x - ψ̂ (ε̂ x)`** in every positive degree.
* `Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity_zero` — the
  degree-zero identity `ĥ (d x) = x - ψ̂ (ε̂ x)`.
* `Crystalline.DividedPowerPolynomial.completedRelativeFormsRetraction_completedCoefficient` —
  **`ε̂ ∘ ψ̂ = id`**, so `ε̂` is a genuine retraction of `ψ̂` and `ψ̂` is injective.
* `..._completedRelativeFormsRetraction_completedDividedPowerDeRham`, in the namespace
  `Crystalline.DividedPowerPolynomial` — **`ε̂` is a map of completed de Rham complexes**, which
  with the two items above is a homotopy equivalence in the full sense.
* `Crystalline.DividedPowerPolynomial.relativeFormsRetraction_coefficientFormsMap` and
  `..._relativeFormsRetraction_dividedPowerDeRham` — the uncompleted `ε ∘ ψ = id` and
  `ε ∘ d = d ∘ ε`, which the two items above complete.  Both are
  consequences of the uncompleted contraction identity rather than inputs to it.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public noncomputable section

open DividedPowers

universe uA uB uW

namespace Crystalline

/-! ### Transporting a contraction across the `p`-adic completion -/

namespace PAdicCompletion

section Transport

variable (p : ℕ) (R : Type*) [CommRing R] {X Y V : Type*} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup V] [Module R V]

/-- **A contraction of a two-term complex of additive maps is carried across the `p`-adic
completion.**

`Crystalline.PAdicCompletion.mapAddHom` is an additive functor on additive maps, so an identity
`h ∘ d + q = id` between maps of the uncompleted modules becomes the same identity between the
completed maps.  Nothing here is about the levels `p^k` separately: one functor is applied to one
identity of maps.

Each completed map is supplied as a *variable* together with an equation identifying it with the
completion of its uncompleted counterpart, rather than being spelled as a completion in the
statement.  That is what makes the lemma usable: at a named divided power ring the two spellings
are definitionally equal but reconciling their instance arguments runs past the heartbeat limit,
whereas here the equations are consumed by `subst` and the rewriting happens where every ring and
every module is a variable and nothing can unfold. -/
theorem mapAddHom_contraction_zero (d : X →+ Y) (h : Y →+ X) (q : X →+ X)
    (D : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := R) p) Y)
    (H : AdicCompletion (pAdicIdeal (A := R) p) Y →+ AdicCompletion (pAdicIdeal (A := R) p) X)
    (Q : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := R) p) X)
    (hD : D = mapAddHom p R R d) (hH : H = mapAddHom p R R h) (hQ : Q = mapAddHom p R R q)
    (hid : h.comp d + q = AddMonoidHom.id X) :
    H.comp D + Q = AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := R) p) X) := by
  subst hD hH hQ
  rw [← mapAddHom_comp p R R R d h, ← mapAddHom_add, hid, mapAddHom_id]

/-- **A contraction of a three-term complex of additive maps is carried across the `p`-adic
completion**: an identity `d₁ ∘ h₁ + h₂ ∘ d₂ + q = id` between maps of the uncompleted modules
becomes the same identity between the completed maps.  See
`Crystalline.PAdicCompletion.mapAddHom_contraction_zero` for why each completed map is a variable
with an equation rather than a spelled-out completion. -/
theorem mapAddHom_contraction (d₁ : X →+ Y) (h₁ : Y →+ X) (d₂ : Y →+ V) (h₂ : V →+ Y)
    (q : Y →+ Y)
    (D₁ : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := R) p) Y)
    (H₁ : AdicCompletion (pAdicIdeal (A := R) p) Y →+ AdicCompletion (pAdicIdeal (A := R) p) X)
    (D₂ : AdicCompletion (pAdicIdeal (A := R) p) Y →+ AdicCompletion (pAdicIdeal (A := R) p) V)
    (H₂ : AdicCompletion (pAdicIdeal (A := R) p) V →+ AdicCompletion (pAdicIdeal (A := R) p) Y)
    (Q : AdicCompletion (pAdicIdeal (A := R) p) Y →+ AdicCompletion (pAdicIdeal (A := R) p) Y)
    (hD₁ : D₁ = mapAddHom p R R d₁) (hH₁ : H₁ = mapAddHom p R R h₁)
    (hD₂ : D₂ = mapAddHom p R R d₂) (hH₂ : H₂ = mapAddHom p R R h₂)
    (hQ : Q = mapAddHom p R R q)
    (hid : d₁.comp h₁ + h₂.comp d₂ + q = AddMonoidHom.id Y) :
    D₁.comp H₁ + H₂.comp D₂ + Q =
      AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := R) p) Y) := by
  subst hD₁ hH₁ hD₂ hH₂ hQ
  rw [← mapAddHom_comp p R R R h₁ d₁, ← mapAddHom_comp p R R R d₂ h₂,
    ← mapAddHom_add, ← mapAddHom_add, hid, mapAddHom_id]

end Transport

section TransportRetraction

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] {X U : Type*}
  [AddCommGroup X] [Module R X] [AddCommGroup U] [Module S U]

/-- **A retraction of additive maps is carried across the `p`-adic completion**, with source and
target modules over two *different* base rings: `g ∘ f = id` becomes `G ∘ F = id`.  As in
`Crystalline.PAdicCompletion.mapAddHom_contraction_zero`, the completed maps are variables
with equations so that nothing has to unfold at the application site. -/
theorem mapAddHom_retraction (f : U →+ X) (g : X →+ U)
    (F : AdicCompletion (pAdicIdeal (A := S) p) U →+ AdicCompletion (pAdicIdeal (A := R) p) X)
    (G : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) U)
    (hF : F = mapAddHom p S R f) (hG : G = mapAddHom p R S g)
    (hid : g.comp f = AddMonoidHom.id U) :
    G.comp F = AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := S) p) U) := by
  subst hF hG
  rw [← mapAddHom_comp p S R S f g, hid, mapAddHom_id]

end TransportRetraction

section TransportSquare

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] {X Y U V : Type*}
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup U] [Module S U]
  [AddCommGroup V] [Module S V]

/-- **A commuting square of additive maps is carried across the `p`-adic completion**, the two
columns being modules over two different base rings: `e' ∘ d = d' ∘ e` becomes `E' ∘ D = D' ∘ E`.
As in `Crystalline.PAdicCompletion.mapAddHom_contraction_zero`, the completed maps are variables
with equations so that nothing has to unfold at the application site. -/
theorem mapAddHom_comm_square (d : X →+ Y) (e : X →+ U) (e' : Y →+ V) (d' : U →+ V)
    (D : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := R) p) Y)
    (E : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) U)
    (E' : AdicCompletion (pAdicIdeal (A := R) p) Y →+ AdicCompletion (pAdicIdeal (A := S) p) V)
    (D' : AdicCompletion (pAdicIdeal (A := S) p) U →+ AdicCompletion (pAdicIdeal (A := S) p) V)
    (hD : D = mapAddHom p R R d) (hE : E = mapAddHom p R S e)
    (hE' : E' = mapAddHom p R S e') (hD' : D' = mapAddHom p S S d')
    (hsq : e'.comp d = d'.comp e) :
    E'.comp D = D'.comp E := by
  subst hD hE hE' hD'
  rw [← mapAddHom_comp p R R S d e', ← mapAddHom_comp p R S S e d', hsq]

end TransportSquare

section TransportScalars

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
  {X Y : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module T Y]

/-- The `p`-adic completion of the identity ring map is the identity. -/
theorem mapRingHom_id_apply (c : AdicCompletion (pAdicIdeal (A := R) p) R) :
    mapRingHom p R R (RingHom.id R) c = c := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R R) (c.val n)
  rw [mapRingHom_val, ← hr, levelMap_mk]
  rfl

/-- Scaling the class of an element of a module by the class of a scalar is the class of the
scaled element, at one level of a `p`-adic filtration. -/
theorem mk_smul_mk (n : ℕ) (s : S) (x : X) :
    (Submodule.Quotient.mk s : S ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S S)) •
        (Submodule.Quotient.mk x : X ⧸ (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S X)) =
      Submodule.Quotient.mk (s • x) :=
  rfl

/-- **The `p`-adic completion of an additive map which is linear over a ground ring `R` is
linear over the completion of `R`.**

The hypothesis is the only one available at the forms of a divided power polynomial algebra: the
relative differential, the relative homotopy and the coefficient retraction are linear over the
base ring `B` of `P = B⟨x_w⟩` and over nothing larger, so their completions are linear over the
`p`-adic completion `D` of `B` and over nothing larger either.  Source and target are modules
over two rings `S` and `T`, each receiving `R` through a ring map, which is what lets the same
statement serve a map of `P`-modules, the retraction `Ωⁿ_P → Ωⁿ_B` and the comparison
`Ωⁿ_B → Ωⁿ_P`.

The scalars are written as `Crystalline.PAdicCompletion.mapRingHom` applied to one element of
`R^∧` rather than as an action of `R^∧`, so that the statement mentions only the module
structures Mathlib's `AdicCompletion` already carries and no restriction of scalars has to be
installed before it can be stated. -/
theorem mapAddHom_smul (f : R →+* S) (g : R →+* T) (u : X →+ Y)
    (hu : ∀ (r : R) (x : X), u (f r • x) = g r • u x)
    (c : AdicCompletion (pAdicIdeal (A := R) p) R)
    (z : AdicCompletion (pAdicIdeal (A := S) p) X) :
    mapAddHom p S T u (mapRingHom p R S f c • z) =
      mapRingHom p R T g c • mapAddHom p S T u z := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R R) (c.val n)
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S X) (z.val n)
  have hcS : (mapRingHom p R S f c).val n = Submodule.Quotient.mk (f r) := by
    rw [mapRingHom_val, ← hr, levelMap_mk]; rfl
  have hcT : (mapRingHom p R T g c).val n = Submodule.Quotient.mk (g r) := by
    rw [mapRingHom_val, ← hr, levelMap_mk]; rfl
  rw [mapAddHom_val, AdicCompletion.smul_eval, hcS, ← hx, mk_smul_mk, levelMap_mk,
    AdicCompletion.smul_eval, hcT, mapAddHom_val, ← hx, levelMap_mk, mk_smul_mk, hu]

/-- **A vanishing bilinear expression stays vanishing across the `p`-adic completion.**

`Crystalline.PAdicCompletion.mapBilinear` is built level by level from the uncompleted bilinear
map, and so is `Crystalline.PAdicCompletion.mapAddHom`, so an identity which holds for every pair
of uncompleted arguments holds at every level of the completion and hence on the completion.

This is what carries the statement that wedging with a coefficient one-form raises the
coefficient degree from `Ω^*_{P/A,δ'}` to `Ω̂^*_{D'}`: the wedge product of the completed forms is
a `mapBilinear`, not the completion of a linear map, so none of the transport lemmas for additive
maps applies to it. -/
theorem mapBilinear_comp_eq_zero {X Y Z V : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] [AddCommGroup V] [Module R V]
    (bil : X →ₗ[R] Y →ₗ[R] Z) (f : X →+ X) (g : Y →+ Y) (h : Z →+ V)
    (hzero : ∀ (u : X) (v : Y), h (bil (f u) (g v)) = 0)
    (x : AdicCompletion (pAdicIdeal (A := R) p) X)
    (y : AdicCompletion (pAdicIdeal (A := R) p) Y) :
    mapAddHom p R R h (mapBilinear p R bil (mapAddHom p R R f x) (mapAddHom p R R g y)) = 0 := by
  refine AdicCompletion.ext fun k ↦ ?_
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ k • ⊤ : Submodule R X) (x.val k)
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ k • ⊤ : Submodule R Y) (y.val k)
  rw [mapAddHom_val, mapBilinear_val, mapAddHom_val, mapAddHom_val, ← hu, ← hv, levelMap_mk,
    levelMap_mk, levelMapBilinear_mk_mk, levelMap_mk, hzero u v,
    AdicCompletion.val_zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)

end TransportScalars

end PAdicCompletion

/-! ### The completed de Rham differential as the completion of an additive map -/

section Generic

variable (p : ℕ) (A : Type uA) [CommRing A] {C : Type*} [CommRing C] [Algebra A C]
  {K : Ideal C} (hK : DividedPowers K)

/-- **The de Rham differential of the completed forms is
`Crystalline.PAdicCompletion.mapAddHom` of the uncompleted one**, which is how
`Crystalline.completedDividedPowerDeRham` is defined.

It is stated as a lemma, with the ring and the divided power structure generic, so that it can be
*rewritten* with: used as a `show … from rfl` at a named divided power ring, the definitional
unfolding has to reconcile the two sets of instance arguments and runs past the heartbeat limit.
Here the rewrite instantiates them by unification with the goal instead. -/
theorem completedDividedPowerDeRham_eq_mapAddHom (i : ℕ) :
    completedDividedPowerDeRham p A hK i =
      PAdicCompletion.mapAddHom p C C (dividedPowerDeRhamHom hK i) :=
  rfl

end Generic

namespace DividedPowerPolynomial

section Completed

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W] (p : ℕ)

/-! ### The retraction is a retraction, uncompleted -/

/-- **The coefficient retraction retracts the comparison of forms**: `ε (ψ ω) = ω`.

`ψ ω` is the generator of the decomposition with no variable differential and the trivial
monomial, by
`Crystalline.DividedPowerPolynomial.decompositionGenerator_zero_zero`, and that is the one slot
the retraction reads.  Together with the contraction identity this is what makes `ψ` a homotopy
equivalence and not merely a map admitting a homotopy; in particular `ψ` is injective. -/
theorem relativeFormsRetraction_coefficientFormsMap (n : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsRetraction A B W n (coefficientFormsMap A B W n omega) = omega :=
  Eq.trans
    (congrArg (fun z : dividedPowerPolynomialForms A B W n ↦
        relativeFormsRetraction A B W n z)
      (decompositionGenerator_zero_zero A B W n rfl (emptyPowersetCard W) omega).symm)
    (relativeFormsRetraction_decompositionGenerator_zero A B W n rfl
      (emptyPowersetCard W) omega)

/-- The uncompleted `ε ∘ ψ = id`, as an identity of additive maps.  This is the shape the
completion consumes. -/
theorem relativeFormsRetraction_comp_coefficientFormsMap (n : ℕ) :
    (relativeFormsRetraction A B W n).toAddMonoidHom.comp
        (coefficientFormsMap A B W n).toAddMonoidHom =
      AddMonoidHom.id (dividedPowerDifferentialForms (A := A) B.dividedPowers n) :=
  AddMonoidHom.ext fun omega ↦ relativeFormsRetraction_coefficientFormsMap A B W n omega

/-- **The comparison of forms is injective**, having the coefficient retraction as a left
inverse.  This is what identifies the retraction's value: an identity between retractions may be
checked after applying `ψ`, where the contraction identity computes both sides. -/
theorem coefficientFormsMap_injective (n : ℕ) :
    Function.Injective (coefficientFormsMap A B W n) :=
  Function.LeftInverse.injective (relativeFormsRetraction_coefficientFormsMap A B W n)

/-! ### The uncompleted contraction identity as an identity of additive maps -/

/-- A sum of two additive endomorphisms is the identity iff the first is `x ↦ x - second x`. -/
private theorem add_eq_id_iff {M : Type*} [AddCommGroup M] (a b : M →+ M) :
    a + b = AddMonoidHom.id M ↔ ∀ x, a x = x - b x :=
  ⟨fun h x ↦ eq_sub_of_add_eq (DFunLike.congr_fun h x),
    fun h ↦ AddMonoidHom.ext fun x ↦ by simp [h x]⟩

/-- **The degree-zero contraction identity, as an identity of additive maps**:
`h₀ ∘ d₀ + ψ ∘ ε = id`.  This is
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity_zero` with the subtraction
moved to the left, which is what the completion functor can be applied to. -/
theorem relativeFormsContraction_addHom_zero :
    (relativeFormsHomotopy A B W 0).toAddMonoidHom.comp
          (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) 0) +
        (coefficientFormsMap A B W 0).toAddMonoidHom.comp
          (relativeFormsRetraction A B W 0).toAddMonoidHom =
      AddMonoidHom.id (dividedPowerPolynomialForms A B W 0) :=
  (add_eq_id_iff _ _).2 (relativeFormsHomotopy_identity_zero A B W)

/-- **The contraction identity in a positive degree, as an identity of additive maps**:
`d ∘ h + h ∘ d + ψ ∘ ε = id`.  This is
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity` with the subtraction moved to
the left, which is what the completion functor can be applied to. -/
theorem relativeFormsContraction_addHom (n : ℕ) :
    (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) n).comp
            (relativeFormsHomotopy A B W n).toAddMonoidHom +
          (relativeFormsHomotopy A B W (n + 1)).toAddMonoidHom.comp
            (dividedPowerDeRhamHom
              (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)) +
        (coefficientFormsMap A B W (n + 1)).toAddMonoidHom.comp
          (relativeFormsRetraction A B W (n + 1)).toAddMonoidHom =
      AddMonoidHom.id (dividedPowerPolynomialForms A B W (n + 1)) :=
  (add_eq_id_iff _ _).2 (relativeFormsHomotopy_identity A B W n)

/-! ### The retraction is a map of complexes, uncompleted -/

/-- **The projection of an exact form**: `ψ ε (d y) = d y - d (h (d y))`.  This is the
contraction identity at `d y`, where the second homotopy term dies because `d ∘ d = 0`. -/
theorem relativeFormsProjection_dividedPowerDeRham (m : ℕ)
    (y : dividedPowerPolynomialForms A B W m) :
    relativeFormsProjection A B W (m + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y -
        dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m
          (relativeFormsHomotopy A B W m
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y)) := by
  have H := relativeFormsHomotopy_identity A B W m
    (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y)
  rw [dividedPowerDeRham_dividedPowerDeRham, map_zero, add_zero] at H
  exact eq_sub_of_add_eq' (eq_sub_iff_add_eq.1 H)

/-- **The differential of the projection in degree zero**: `d (ψ ε y) = d y - d (h (d y))`, from
the degree-zero contraction identity. -/
theorem dividedPowerDeRham_relativeFormsProjection_zero
    (y : dividedPowerPolynomialForms A B W 0) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0
        (relativeFormsProjection A B W 0 y) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0 y -
        dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0
          (relativeFormsHomotopy A B W 0
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0 y)) := by
  have hP : relativeFormsProjection A B W 0 y =
      y - relativeFormsHomotopy A B W 0
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0 y) := by
    exact eq_sub_of_add_eq' (eq_sub_iff_add_eq.1 (relativeFormsHomotopy_identity_zero A B W y))
  rw [hP, dividedPowerDeRham_sub]

/-- **The differential of the projection in a positive degree**: `d (ψ ε y) = d y - d (h (d y))`,
from the contraction identity at `y`, the term `d (d (h y))` dying because `d ∘ d = 0`. -/
theorem dividedPowerDeRham_relativeFormsProjection_succ (k : ℕ)
    (y : dividedPowerPolynomialForms A B W (k + 1)) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (k + 1)
        (relativeFormsProjection A B W (k + 1) y) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (k + 1) y -
        dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (k + 1)
          (relativeFormsHomotopy A B W (k + 1)
            (dividedPowerDeRham
              (setIndexedDividedPowerPolynomialDividedPowers B W) (k + 1) y)) := by
  have hP : relativeFormsProjection A B W (k + 1) y =
      y - (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) k
          (relativeFormsHomotopy A B W k y) +
        relativeFormsHomotopy A B W (k + 1)
          (dividedPowerDeRham
            (setIndexedDividedPowerPolynomialDividedPowers B W) (k + 1) y)) := by
    exact eq_sub_of_add_eq' (eq_sub_iff_add_eq.1 (relativeFormsHomotopy_identity A B W k y))
  rw [hP, dividedPowerDeRham_sub, dividedPowerDeRham_add,
    dividedPowerDeRham_dividedPowerDeRham, zero_add]

/-- **The projection commutes with the de Rham differential**, in every degree: the two previous
computations have the same right-hand side. -/
theorem dividedPowerDeRham_relativeFormsProjection (m : ℕ)
    (y : dividedPowerPolynomialForms A B W m) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m
        (relativeFormsProjection A B W m y) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y -
        dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m
          (relativeFormsHomotopy A B W m
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y)) := by
  cases m with
  | zero => exact dividedPowerDeRham_relativeFormsProjection_zero A B W y
  | succ k => exact dividedPowerDeRham_relativeFormsProjection_succ A B W k y

/-- **The coefficient retraction is a map of de Rham complexes**: `ε (d y) = d (ε y)`.

This is not an extra input to the Poincaré lemma but a consequence of it.  `ψ` is injective,
having `ε` as a left inverse, so it is enough to check the identity after applying `ψ`; there it
reads `ψ ε (d y) = d (ψ ε y)`, and the contraction identity computes both sides to
`d y - d (h (d y))`.  With this and
`Crystalline.DividedPowerPolynomial.coefficientFormsMap_dividedPowerDeRham` both `ψ` and `ε` are
maps of complexes, so the contraction identity is a homotopy equivalence in the full sense. -/
theorem relativeFormsRetraction_dividedPowerDeRham (m : ℕ)
    (y : dividedPowerPolynomialForms A B W m) :
    relativeFormsRetraction A B W (m + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) m y) =
      dividedPowerDeRham B.dividedPowers m (relativeFormsRetraction A B W m y) := by
  refine coefficientFormsMap_injective A B W (m + 1) ?_
  rw [← relativeFormsProjection_apply, coefficientFormsMap_dividedPowerDeRham,
    ← relativeFormsProjection_apply, relativeFormsProjection_dividedPowerDeRham,
    dividedPowerDeRham_relativeFormsProjection]

/-- The uncompleted commuting square `ε ∘ d = d ∘ ε`, as an identity of additive maps.  This is
the shape the completion consumes. -/
theorem relativeFormsRetraction_comp_dividedPowerDeRhamHom (m : ℕ) :
    (relativeFormsRetraction A B W (m + 1)).toAddMonoidHom.comp
        (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) m) =
      (dividedPowerDeRhamHom B.dividedPowers m).comp
        (relativeFormsRetraction A B W m).toAddMonoidHom :=
  AddMonoidHom.ext fun y ↦ relativeFormsRetraction_dividedPowerDeRham A B W m y

/-! ### The completed homotopy, retraction and comparison -/

/-- **The completed contracting homotopy `ĥ : Ω̂^{n+1}_{D'} → Ω̂^n_{D'}`**, the `p`-adic completion
of the homotopy of `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy`.

It is `Crystalline.PAdicCompletion.mapAddHom` and not `AdicCompletion.map` of anything: the
homotopy is `A`-linear and not `P`-linear, exactly as the de Rham differential it contracts is
not. -/
def completedRelativeFormsHomotopy (n : ℕ) :
    completedPolynomialForms A B W p (n + 1) →+ completedPolynomialForms A B W p n :=
  PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (relativeFormsHomotopy A B W n).toAddMonoidHom

/-- The completed homotopy, unfolded.  Stated as a lemma with every argument explicit so that it
can be rewritten with at no unification cost: `rw` against the definition itself has to solve for
the implicit ring and instance arguments and runs past the heartbeat limit. -/
theorem completedRelativeFormsHomotopy_eq (n : ℕ) :
    completedRelativeFormsHomotopy A B W p n =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (relativeFormsHomotopy A B W n).toAddMonoidHom :=
  rfl

/-- The completed homotopy extends the uncompleted one, which pins it down: the image of
`Ω^{n+1}_{P/A,δ'}` is `p`-adically dense. -/
@[simp] theorem completedRelativeFormsHomotopy_of (n : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    completedRelativeFormsHomotopy A B W p n (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (relativeFormsHomotopy A B W n x) :=
  PAdicCompletion.mapAddHom_of p _ _ _ x

/-- **The completed coefficient retraction `ε̂ : Ω̂^n_{D'} → Ω̂^n_D`**, the `p`-adic completion of
`Crystalline.DividedPowerPolynomial.relativeFormsRetraction`.

Source and target are modules over the two *different* rings `P` and `B`, which is why
`AdicCompletion.map` does not apply even though the retraction happens to be `A`-linear:
completion along `(p)` is functorial for additive maps across different base rings. -/
def completedRelativeFormsRetraction (n : ℕ) :
    completedPolynomialForms A B W p n →+ completedDividedPowerForms p A B.dividedPowers n :=
  PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB)
    (relativeFormsRetraction A B W n).toAddMonoidHom

/-- The completed retraction, unfolded, with every argument explicit; see
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_eq` for why this is a lemma. -/
theorem completedRelativeFormsRetraction_eq (n : ℕ) :
    completedRelativeFormsRetraction A B W p n =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB)
        (relativeFormsRetraction A B W n).toAddMonoidHom :=
  rfl

/-- The completed retraction extends the uncompleted one. -/
@[simp] theorem completedRelativeFormsRetraction_of (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    completedRelativeFormsRetraction A B W p n (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (relativeFormsRetraction A B W n x) :=
  PAdicCompletion.mapAddHom_of p _ _ _ x

/-- **The completed comparison `ψ̂ : Ω̂^n_D → Ω̂^n_{D'}`** of completed de Rham complexes along the
coefficient inclusion `B → P`.

This is not a new construction: it is the library's `Crystalline.completedMapDifferentialForms`
at the divided power morphism `Crystalline.DividedPowerPolynomial.coefficientAlgHom`, so every
lemma proved about that comparison — in particular that it respects the de Rham differential,
`Crystalline.completedMapDifferentialForms_deRham` — applies verbatim.  It is semilinear over
`algebraMap B P` and not linear, since its source and target are modules over different rings. -/
abbrev completedCoefficientFormsMap (n : ℕ) :
    completedDividedPowerForms p A B.dividedPowers n →ₛₗ[(coefficientAlgHom A B W).toRingHom]
      completedPolynomialForms A B W p n :=
  completedMapDifferentialForms p A B.dividedPowers
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) n

omit [LinearOrder W] in
/-- **The completed comparison of forms is the completion of the uncompleted comparison**, read as
an additive map.  This is the one spelling crossing the proof below needs, and it is paid here
once: `Crystalline.completedMapDifferentialForms` is built from `Crystalline.adicCompletionMapₛₗ`
and the contraction is transported by `Crystalline.PAdicCompletion.mapAddHom`, and the two agree
because both are determined by their values at the levels. -/
theorem completedCoefficientFormsMap_toAddMonoidHom (n : ℕ) :
    (completedCoefficientFormsMap A B W p n).toAddMonoidHom =
      PAdicCompletion.mapAddHom p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (coefficientFormsMap A B W n).toAddMonoidHom :=
  PAdicCompletion.mapAddHom_eq_of_val p (B : Type uB)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (coefficientFormsMap A B W n).toAddMonoidHom _
    fun m z omega hz ↦
      completedMapDifferentialForms_val p A B.dividedPowers
        (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
        (coefficientAlgHom_isDPMorphism A B W) n m z omega hz

/-- **The projection `ψ̂ ∘ ε̂` of the completed forms onto the completed coefficient forms.** -/
def completedRelativeFormsProjection (n : ℕ) :
    completedPolynomialForms A B W p n →+ completedPolynomialForms A B W p n :=
  (completedCoefficientFormsMap A B W p n).toAddMonoidHom.comp
    (completedRelativeFormsRetraction A B W p n)

/-- The projection is the completed comparison after the completed retraction. -/
theorem completedRelativeFormsProjection_apply (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedRelativeFormsProjection A B W p n x =
      completedCoefficientFormsMap A B W p n (completedRelativeFormsRetraction A B W p n x) :=
  rfl

/-- The projection is the completion of the uncompleted projection: the two completions, one
along `(p) ⊆ P` and one along `(p) ⊆ B`, compose to the completion of the composite. -/
theorem completedRelativeFormsProjection_eq (n : ℕ) :
    completedRelativeFormsProjection A B W p n =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        ((coefficientFormsMap A B W n).toAddMonoidHom.comp
          (relativeFormsRetraction A B W n).toAddMonoidHom) :=
  Eq.trans
    (congrArg (fun g : completedDividedPowerForms p A B.dividedPowers n →+
          completedPolynomialForms A B W p n ↦
        g.comp (completedRelativeFormsRetraction A B W p n))
      (completedCoefficientFormsMap_toAddMonoidHom A B W p n))
    (PAdicCompletion.mapAddHom_comp p (setIndexedDividedPowerPolynomialAlgebra B W)
      (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
      (relativeFormsRetraction A B W n).toAddMonoidHom
      (coefficientFormsMap A B W n).toAddMonoidHom).symm

/-! ### `ε̂` is a retraction of `ψ̂` -/

/-- **`ε̂ ∘ ψ̂ = id`**: the completed coefficient retraction retracts the completed comparison, so
`ψ̂` is injective and is a genuine homotopy equivalence of completed de Rham complexes rather than
merely a map admitting a homotopy.  It is the completion of
`Crystalline.DividedPowerPolynomial.relativeFormsRetraction_comp_coefficientFormsMap`. -/
theorem completedRelativeFormsRetraction_comp_completedCoefficient (n : ℕ) :
    (completedRelativeFormsRetraction A B W p n).comp
        (completedCoefficientFormsMap A B W p n).toAddMonoidHom =
      AddMonoidHom.id (completedDividedPowerForms p A B.dividedPowers n) :=
  PAdicCompletion.mapAddHom_retraction p (setIndexedDividedPowerPolynomialAlgebra B W)
    (B : Type uB) (coefficientFormsMap A B W n).toAddMonoidHom
    (relativeFormsRetraction A B W n).toAddMonoidHom
    (completedCoefficientFormsMap A B W p n).toAddMonoidHom
    (completedRelativeFormsRetraction A B W p n)
    (completedCoefficientFormsMap_toAddMonoidHom A B W p n)
    (completedRelativeFormsRetraction_eq A B W p n)
    (relativeFormsRetraction_comp_coefficientFormsMap A B W n)

/-- `ε̂ (ψ̂ x) = x`, read on an element. -/
theorem completedRelativeFormsRetraction_completedCoefficient (n : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers n) :
    completedRelativeFormsRetraction A B W p n (completedCoefficientFormsMap A B W p n x) = x :=
  DFunLike.congr_fun (completedRelativeFormsRetraction_comp_completedCoefficient A B W p n) x

/-! ### `ε̂` is a map of completed de Rham complexes -/

/-- **The completed coefficient retraction is a map of completed de Rham complexes**, as an
identity of additive maps: `ε̂ ∘ d = d ∘ ε̂`.  It is the completion of
`Crystalline.DividedPowerPolynomial.relativeFormsRetraction_comp_dividedPowerDeRhamHom`, the two
columns of the square being modules over the different rings `P` and `B`. -/
theorem completedRelativeFormsRetraction_comp_completedDeRham (m : ℕ) :
    (completedRelativeFormsRetraction A B W p (m + 1)).comp
        (completedDividedPowerDeRham p A
          (setIndexedDividedPowerPolynomialDividedPowers B W) m) =
      (completedDividedPowerDeRham p A B.dividedPowers m).comp
        (completedRelativeFormsRetraction A B W p m) :=
  PAdicCompletion.mapAddHom_comm_square p (setIndexedDividedPowerPolynomialAlgebra B W)
    (B : Type uB)
    (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) m)
    (relativeFormsRetraction A B W m).toAddMonoidHom
    (relativeFormsRetraction A B W (m + 1)).toAddMonoidHom
    (dividedPowerDeRhamHom B.dividedPowers m)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) m)
    (completedRelativeFormsRetraction A B W p m)
    (completedRelativeFormsRetraction A B W p (m + 1))
    (completedDividedPowerDeRham p A B.dividedPowers m)
    (completedDividedPowerDeRham_eq_mapAddHom p A
      (setIndexedDividedPowerPolynomialDividedPowers B W) m)
    (completedRelativeFormsRetraction_eq A B W p m)
    (completedRelativeFormsRetraction_eq A B W p (m + 1))
    (completedDividedPowerDeRham_eq_mapAddHom p A B.dividedPowers m)
    (relativeFormsRetraction_comp_dividedPowerDeRhamHom A B W m)

/-- **`ε̂ (d x) = d (ε̂ x)`**: the completed coefficient retraction is a map of completed de Rham
complexes, read on an element.  Together with
`Crystalline.completedMapDifferentialForms_deRham` for `ψ̂` this makes the contraction identity a
homotopy equivalence of completed de Rham complexes in the full sense: both comparison maps are
maps of complexes, `ε̂ ∘ ψ̂ = id`, and `ψ̂ ∘ ε̂` is homotopic to the identity. -/
theorem completedRelativeFormsRetraction_completedDividedPowerDeRham (m : ℕ)
    (x : completedPolynomialForms A B W p m) :
    completedRelativeFormsRetraction A B W p (m + 1)
        (completedDividedPowerDeRham p A
          (setIndexedDividedPowerPolynomialDividedPowers B W) m x) =
      completedDividedPowerDeRham p A B.dividedPowers m
        (completedRelativeFormsRetraction A B W p m x) :=
  DFunLike.congr_fun
    (completedRelativeFormsRetraction_comp_completedDeRham A B W p m) x

/-! ### The completed contraction identity -/

/-- **The degree-zero completed contraction identity, as an identity of additive maps**:
`ĥ₀ ∘ d₀ + ψ̂ ∘ ε̂ = id` on `Ω̂^0_{D'}`. -/
theorem completedRelativeFormsContraction_addHom_zero :
    (completedRelativeFormsHomotopy A B W p 0).comp
          (completedDividedPowerDeRham p A
            (setIndexedDividedPowerPolynomialDividedPowers B W) 0) +
        completedRelativeFormsProjection A B W p 0 =
      AddMonoidHom.id (completedPolynomialForms A B W p 0) :=
  PAdicCompletion.mapAddHom_contraction_zero p
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) 0)
    (relativeFormsHomotopy A B W 0).toAddMonoidHom
    ((coefficientFormsMap A B W 0).toAddMonoidHom.comp
      (relativeFormsRetraction A B W 0).toAddMonoidHom)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) 0)
    (completedRelativeFormsHomotopy A B W p 0)
    (completedRelativeFormsProjection A B W p 0)
    (completedDividedPowerDeRham_eq_mapAddHom p A
      (setIndexedDividedPowerPolynomialDividedPowers B W) 0)
    (completedRelativeFormsHomotopy_eq A B W p 0)
    (completedRelativeFormsProjection_eq A B W p 0)
    (relativeFormsContraction_addHom_zero A B W)

/-- **The completed contraction identity in a positive degree, as an identity of additive maps**:
`d ∘ ĥ + ĥ ∘ d + ψ̂ ∘ ε̂ = id` on `Ω̂^{n+1}_{D'}`.

Every term is the `p`-adic completion of the corresponding uncompleted term, and
`Crystalline.PAdicCompletion.mapAddHom` is an additive functor, so this *is* the uncompleted
identity `Crystalline.DividedPowerPolynomial.relativeFormsContraction_addHom`. -/
theorem completedRelativeFormsContraction_addHom (n : ℕ) :
    (completedDividedPowerDeRham p A
              (setIndexedDividedPowerPolynomialDividedPowers B W) n).comp
            (completedRelativeFormsHomotopy A B W p n) +
          (completedRelativeFormsHomotopy A B W p (n + 1)).comp
            (completedDividedPowerDeRham p A
              (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)) +
        completedRelativeFormsProjection A B W p (n + 1) =
      AddMonoidHom.id (completedPolynomialForms A B W p (n + 1)) :=
  PAdicCompletion.mapAddHom_contraction p
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) n)
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (dividedPowerDeRhamHom (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1))
    (relativeFormsHomotopy A B W (n + 1)).toAddMonoidHom
    ((coefficientFormsMap A B W (n + 1)).toAddMonoidHom.comp
      (relativeFormsRetraction A B W (n + 1)).toAddMonoidHom)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) n)
    (completedRelativeFormsHomotopy A B W p n)
    (completedDividedPowerDeRham p A
      (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1))
    (completedRelativeFormsHomotopy A B W p (n + 1))
    (completedRelativeFormsProjection A B W p (n + 1))
    (completedDividedPowerDeRham_eq_mapAddHom p A
      (setIndexedDividedPowerPolynomialDividedPowers B W) n)
    (completedRelativeFormsHomotopy_eq A B W p n)
    (completedDividedPowerDeRham_eq_mapAddHom p A
      (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1))
    (completedRelativeFormsHomotopy_eq A B W p (n + 1))
    (completedRelativeFormsProjection_eq A B W p (n + 1))
    (relativeFormsContraction_addHom A B W n)

/-- **The degree-zero half of the completed contraction identity**: `ĥ (d x) = x - ψ̂ (ε̂ x)`. -/
theorem completedRelativeFormsHomotopy_identity_zero
    (x : completedPolynomialForms A B W p 0) :
    completedRelativeFormsHomotopy A B W p 0
        (completedDividedPowerDeRham p A
          (setIndexedDividedPowerPolynomialDividedPowers B W) 0 x) =
      x - completedRelativeFormsProjection A B W p 0 x :=
  (add_eq_id_iff _ _).1 (completedRelativeFormsContraction_addHom_zero A B W p) x

/-- **The relative divided power Poincaré lemma over the `p`-adic completion, as a homotopy
equivalence.**

`d (ĥ x) + ĥ (d x) = x - ψ̂ (ε̂ x)`: the comparison `ψ̂ : Ω̂^*_D → Ω̂^*_{D'}` of the completed
divided power de Rham complexes along `B → P = B⟨x_w : w ∈ W⟩` is a homotopy equivalence, with
retraction the completed coefficient retraction `ε̂` of
`Crystalline.DividedPowerPolynomial.completedRelativeFormsRetraction_completedCoefficient`.

This is an identity between maps of the completions `Ω̂^n_{D'}`, not a family of identities at the
levels `p^k`; see the module docstring for why the transfer is legitimate and why no limit
argument is involved.  The divided power ideal `I` of the base is arbitrary and `W` is an
arbitrary family of variables, as in the uncompleted
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity`.

This is an ingredient of the clause of [Stacks, Tag 07LD] over the `p`-adic completions, at the
forms themselves.  For a `D`-module `M` with an integrable connection the comparison of the twisted
de Rham complexes is a quasi-isomorphism by
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`; the homotopy `ĥ` here is
the one the perturbation argument there perturbs, and it satisfies that argument's three side
conditions by
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_completedRelativeFormsHomotopy`
and its two companions. -/
theorem completedRelativeFormsHomotopy_identity (n : ℕ)
    (x : completedPolynomialForms A B W p (n + 1)) :
    completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (completedRelativeFormsHomotopy A B W p n x) +
        completedRelativeFormsHomotopy A B W p (n + 1)
          (completedDividedPowerDeRham p A
            (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1) x) =
      x - completedRelativeFormsProjection A B W p (n + 1) x :=
  eq_sub_of_add_eq (DFunLike.congr_fun (completedRelativeFormsContraction_addHom A B W p n) x)

end Completed

end DividedPowerPolynomial

end Crystalline

end
