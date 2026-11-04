module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormula
public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionPairing
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
public import StacksFrontier.AlgebraicGeometry.Curves.Models.TrivialTensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Connected
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksCore.Tactic.StacksAttribute

/-!
# The filtration of the reduced special fibre by single components

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve over the fraction field
of a discrete valuation ring and write the special fibre as a sum of effective Cartier divisors
`X_k = Σ mᵢ Cᵢ`.  Put `d = gcd(m₁, …, mₙ)` and let `D = Σ (mᵢ/d) Cᵢ`.  Then `D` is reached from
the reduction `(X_k)_red = Σ Cᵢ` by adding one component at a time,

`(X_k)_red = Z₀ ⊆ Z₁ ⊆ … ⊆ Z_M = D`,  `Z_{j+1} = Z_j + C_{i_j}`,

in such a way that `H⁰(Z_j, 𝒪_{Z_j})` is a field finite over the residue field `k` at every
stage.  This is the geometric input of the Artin–Winters bound on the multiplicities of a
regular model.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.fibreSubschemeToSpec` — the structure morphism over
  the residue field of a closed subscheme of `X` containing the special fibre
  scheme-theoretically.
* `Stacks.Models.RegularProperModelSituation.fibreSubschemeResidueMap` and
  `Stacks.Models.RegularProperModelSituation.fibreSubschemeBaseMap` — the induced maps
  `k ⟶ Γ(Z, 𝒪_Z)` and `R ⟶ Γ(Z, 𝒪_Z)` on global functions.

## Main results

* `Stacks.Models.exists_chain_reducedSpecialFibre` — **Stacks Tag 0C68**, the filtration above.
* `Stacks.Models.isField_globalSections_of_connectedSpace` — the global functions of a connected
  reduced proper scheme over a field form a field.
* `Stacks.Models.not_supportSet_subset_of_radical_eq_prod` — distinct components of a
  decomposition whose sum is reduced are incomparable.
* `Stacks.Models.decompositionMatrix_nonneg_and_eq_zero_iff`,
  `Stacks.Models.decompositionMatrix_comm`,
  `Stacks.Models.decompositionMatrix_mulVec_multiplicity`,
  `Stacks.Models.decompositionMatrix_connected`,
  `Stacks.Models.decompositionForm_nonpos_and_eq_zero_iff` — the four properties of
  [Stacks, Tag 0C66] read at the decomposition `X_k = Σ mᵢCᵢ` that the statement of Tag 0C68
  is given.
* `Stacks.Models.exists_componentDegree_negativeTwist_neg` — the geometric step of the induction:
  at every stage short of `Σ (mᵢ/d)Cᵢ` some component still to be added has
  `deg(𝒪_X(-Z_t)|_{Cᵢ}) < 0`.

## Implementation notes

**Beware the notation.** On `AlgebraicGeometry.Scheme.IdealSheafData` the sum of divisors is the
product `*` of ideal sheaves and the `n`-fold sum `nD` is the power `^`, so `Σ aᵢ Cᵢ` is written
`∏ i ∈ s, C i ^ a i`; Mathlib's `Add` is `⊔`, which is scheme-theoretic intersection.  Inclusion
of closed subschemes is the *reverse* order on ideal sheaf data, so the chain
`Z₀ ⊆ Z₁ ⊆ … ⊆ Z_M` reads `Z (j + 1) ≤ Z j`.

**Relative to a decomposition.**  As in
`StacksFrontier/AlgebraicGeometry/Curves/Models/ReducedSpecialFibre.lean`, the components and their
multiplicities are not constructed here: a finite index set `s`, a family `C` of effective
Cartier divisors and multiplicities `m` with `X_k = ∏ i ∈ s, C i ^ m i` enter as hypotheses,
which is exactly the phrase "write `X_k = Σ mᵢ Cᵢ`" opening Situation
[Stacks, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61).  The reduction `(X_k)_red` is the
reduced induced structure `S.specialFiberIdeal.radical` on the support of the special fibre, and
the hypothesis `hred` is the remaining part of [Stacks, Tag 0C5Z], that this reduction is the sum
`Σ Cᵢ` of the components with multiplicity one.

**The algebra structure over the residue field is canonical, not chosen.**  Every closed
subscheme `Z` of `X` containing the special fibre scheme-theoretically (that is
`S.specialFiberIdeal ≤ Z` on ideal sheaf data) factors through the special fibre by
`AlgebraicGeometry.IsClosedImmersion.lift`, hence carries a structure morphism to `Spec(k)`, and
`fibreSubschemeResidueMap` is the induced map on global functions.  It is pinned down by
`fibreSubschemeResidueMap_comp`: composed with `R ⟶ k` it is the canonical `R ⟶ Γ(Z, 𝒪_Z)`, and
`R ⟶ k` is surjective, so no other homomorphism out of `k` does that.  The statement below
therefore asserts the existence of a `k`-algebra structure *compatible with the base ring*, not
of an arbitrary one.

**Every input of the induction is proved.**  The source's proof composes five cited results, and
all five are available here.

* Connectedness of the reduced special fibre is [Stacks, Tag 0C62],
  `Stacks.Models.RegularProperModelSituation.connectedSpace_subscheme_radical_specialFiberIdeal`
  of `StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberConnected.lean`, read on the
  reduction, which has the same underlying topological space as the special fibre
  (`AlgebraicGeometry.Scheme.IdealSheafData.support_radical`).  With it, the base case `Z₀` is
  `isField_globalSections_of_connectedSpace` below: the global functions of a connected reduced
  proper scheme over a field form a field, which is the *field* clause of [Stacks, Tag 0BUG].
* Finiteness of those global functions over `k` is clause (1) of [Stacks, Tag 0BUG],
  `Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper`.
* Finite dimensionality of coherent cohomology over a field is [Stacks, Tag 02O6], used at the
  structure sheaf of a component as
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_unit`; it is what part (1) of
  [Stacks, Tag 0B40] needs.
* [Stacks, Tag 0C4T], the sequence `0 ⟶ 𝒪_X(-Z_t)|_{Cᵢ} ⟶ 𝒪_{Z_t + Cᵢ} ⟶ 𝒪_{Z_t} ⟶ 0`, is
  `Stacks.Divisors.addEffectiveCartierDivisor_shortExact`.  Sections over the whole space are
  left exact, `Stacks.Algebraization.exists_app_eq_of_shortExact`, so the vanishing of
  `H⁰(Cᵢ, 𝒪_X(-Z_t)|_{Cᵢ})` makes `Γ(Z_t + Cᵢ, 𝒪) ⟶ Γ(Z_t, 𝒪)` injective; the restriction map of
  the sequence is the map of global functions of the inclusion of closed subschemes by
  `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_app_top`.
* Part (1) of [Stacks, Tag 0B40], that an invertible module with a nonzero global section on an
  integral proper curve has nonnegative degree, is
  `AlgebraicGeometry.invertibleCurveDegree_nonneg_of_eval_top_ne_zero`; read contrapositively, a
  negative degree annihilates every global section of `𝒪_X(-Z_t)|_{Cᵢ}`.

**The geometric step, and why it is redone at the given decomposition.**  The source's inductive
step is: given `Z_t = Σ aᵢCᵢ` with `1 ≤ aᵢ ≤ mᵢ/d` and `a` not yet equal to `m/d`, the
self-intersection `(Z_t · Z_t)` is negative while `(D · Z_t) = 0`, so some `i` with `aᵢ < mᵢ/d`
has `(Cᵢ · Z_t) > 0`, and then `deg(𝒪_X(-Z_t)|_{Cᵢ}) = -(Cᵢ · Z_t) < 0`.  That is
`exists_componentDegree_negativeTwist_neg`, and the sign is moved onto the other argument of the
pairing by `Stacks.Models.componentDegree_negativeTwist_eq_neg`, the invertible case of
[Stacks, Tag 0AYX], whose own hypothesis is discharged by
`Stacks.Models.componentDegreeAdditive`.

The negativity of `(Z_t · Z_t)` is part (4) of [Stacks, Tag 0C66], whose statement in
`StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean` is indexed by the
*irreducible components* of the special fibre.  Tag 0C68 is stated above at an arbitrary
decomposition `X_k = Σᵢ∈ₛ mᵢCᵢ` into integral proper curves, so the four properties are proved
again here at that family, by the route of
`StacksFrontier/AlgebraicGeometry/Curves/Models/IntersectionForm.lean`:
`decompositionMatrix_nonneg_and_eq_zero_iff` is part (1), `decompositionMatrix_comm` the symmetry
of [Stacks, Tag 0C64], `decompositionMatrix_mulVec_multiplicity` part (2),
`decompositionMatrix_connected` part (3), and `decompositionForm_nonpos_and_eq_zero_iff` part (4)
through `Stacks.Models.intersectionForm_nonpos_of_properties` and
`Stacks.Models.intersectionForm_eq_zero_iff_of_properties`.  The entries are taken at the
*canonical* structure morphism `fibreSubschemeToSpec` of each component rather than at the given
`g`: every `Cᵢ` contains the special fibre scheme-theoretically, because every `mᵢ` is positive
(`specialFiberIdeal_le_of_mem`), so it has one, and these all factor through the closed immersion
of the special fibre, which is a monomorphism — that is what makes the matrix symmetric, and no
hypothesis relates the given `g` to the model.

Part (1) needs distinct components to be incomparable, which for the irreducible components is
immediate and for an arbitrary family is `not_supportSet_subset_of_radical_eq_prod`: a containment
`Cᵢ ⊆ Cⱼ` makes the index `i` redundant in the intersection `⋂ Cₗ`, which the radicality of
`Σ Cₗ` — the hypothesis `hred` — identifies with the product `∏ Cₗ`; the product `Q` over the
remaining indices then satisfies `Q = Cᵢ · Q`, and Nakayama's lemma at a point of `Cᵢ` forces the
stalk of `Q` there to vanish, which the local equation of the effective Cartier divisor `Q`
forbids.  Part (3) needs the components to cover the special fibre, which `hred` also gives.

**Where the arithmetic goes.**  `Stacks.Models.exists_pos_sum_of_lt_div_gcd` is the purely
numerical half of the geometric step: that `e = m/d - a` is not a rational multiple of `m`, which
is the Bézout computation `Stacks.Models.exists_gcd_mul_eq_mul`, and the passage from a strictly
negative quadratic form to a single positive summand.  What the proof of Tag 0C68 contributes
beyond the cited results is then the induction itself: the chain of coefficient families from `1`
to `m/d`, the divisor bookkeeping, and the propagation of "a field finite over `k`" along an
injective restriction map, which is the appeal to [Stacks, Tag 00GR] in the source.

## References

* [Stacks Project, Tag 0C68](https://stacks.math.columbia.edu/tag/0C68)
* [Artin and Winters, *Degenerate fibres and stable reduction of curves*, Lemma 2.6]
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 00GR](https://stacks.math.columbia.edu/tag/00GR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProperGeomConnected
open Stacks.AlgebraicGeometry.ProperSectionsGeom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Divisor bookkeeping for sums `Σ aᵢ Cᵢ` of components -/

variable {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData)

/-- **`Σ aᵢ Cᵢ ⊆ Σ bᵢ Cᵢ` for `a ≤ b`.** Sums of the same components are ordered oppositely to
their coefficient families, since containment of closed subschemes reverses the inequality of
their sheaves of ideals. -/
theorem prod_pow_le_prod_pow_of_le {a b : ι → ℕ} (h : ∀ i ∈ s, a i ≤ b i) :
    ∏ i ∈ s, C i ^ b i ≤ ∏ i ∈ s, C i ^ a i :=
  Finset.prod_le_prod (fun _ _ => bot_le) (fun i hi => pow_le_pow_right_of_le (C i) (h i hi))

/-- Increasing one coefficient by one adds the corresponding component:
`Σ a'ⱼ Cⱼ = Σ aⱼ Cⱼ + Cᵢ` when `a'ᵢ = aᵢ + 1` and `a'` agrees with `a` elsewhere. -/
theorem prod_pow_succ_at {a a' : ι → ℕ} {i : ι} (hi : i ∈ s) (hai : a' i = a i + 1)
    (hane : ∀ j ∈ s, j ≠ i → a' j = a j) :
    ∏ j ∈ s, C j ^ a' j = (∏ j ∈ s, C j ^ a j) * C i := by
  classical
  have herase : (∏ j ∈ s.erase i, C j ^ a' j) = ∏ j ∈ s.erase i, C j ^ a j :=
    Finset.prod_congr rfl fun j hj => by
      rw [hane j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase s _ hi, ← Finset.mul_prod_erase s (fun j => C j ^ a j) hi,
    hai, pow_succ, herase]
  ring

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Models

open Stacks.Divisors
open AlgebraicGeometry.Scheme.IdealSheafData (mul_le_left prod_pow_le_prod_pow_of_le
  prod_pow_succ_at)

/-! ### Global functions on a connected reduced proper scheme over a field -/

/-- **The global functions of a connected reduced proper scheme over a field form a field**, the
field clause of [Stacks, Tag 0BUG].  They are reduced because the scheme is, integral over the
base field because the structure morphism is universally closed, and have irreducible spectrum
because that spectrum is connected and the ring is integral over a field; reduced with
irreducible spectrum makes the ring a domain, and a domain integral over a field is a field. -/
theorem isField_globalSections_of_connectedSpace (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsProper g] [IsReduced Y] [ConnectedSpace Y] : IsField Γ(Y, ⊤) := by
  let alg : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hint : Algebra.IsIntegral k Γ(Y, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact isIntegral_toSpecΓ_algebraMap g x⟩
  have hred : _root_.IsReduced Γ(Y, ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  have hconnSpec : ConnectedSpace (Spec Γ(Y, ⊤)) := by
    rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr (surjective_toSpecΓ (k := k) g)]
    exact isConnected_range Y.toSpecΓ.continuous
  have hconnPrime : ConnectedSpace (PrimeSpectrum Γ(Y, ⊤)) := hconnSpec
  have hirrSpec : IrreducibleSpace (Spec Γ(Y, ⊤)) :=
    irreducibleSpace_primeSpectrum_of_isIntegral k Γ(Y, ⊤)
  have hredSpec : IsReduced (Spec Γ(Y, ⊤)) := (affine_isReduced_iff _).mpr hred
  have hdom : IsDomain Γ(Y, ⊤) :=
    (affine_isIntegral_iff _).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  exact isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)

/-- **A subring of a field which is finite over a base field is again a field finite over it.**
If an injective ring map `A ⟶ B` into a field is compatible with homomorphisms from a field `k`
and `B` is finite over `k`, then `A` is a field and is finite over `k`.  This is the appeal to
[Stacks, Tag 00GR] in the source: a `k`-subalgebra of a finite field extension of `k` is a
field. -/
private theorem isField_and_finite_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (k : Type u) [Field k] (φ : k →+* A) (ψ : k →+* B) (res : A →+* B) (hres : res.comp φ = ψ)
    (hinj : Function.Injective res) (hB : IsField B) (hψ : ψ.Finite) :
    IsField A ∧ φ.Finite := by
  let algA : Algebra k A := φ.toAlgebra
  let algB : Algebra k B := ψ.toAlgebra
  let fieldB : Field B := hB.toField
  have hfinB : Module.Finite k B := hψ
  have hnoeth : IsNoetherian k B := isNoetherian_of_isNoetherianRing_of_finite k B
  let f : A →ₐ[k] B := { res with commutes' := fun c => RingHom.congr_fun hres c }
  have hfinA : Module.Finite k A := Module.Finite.of_injective f.toLinearMap hinj
  have hdomA : IsDomain A := hinj.isDomain res
  have hintA : Algebra.IsIntegral k A := Algebra.IsIntegral.of_finite k A
  exact ⟨isField_of_isIntegral_of_isField' (Field.toIsField k), hfinA⟩

/-! ### Closed subschemes of the special fibre as schemes over the residue field -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) (Z : S.X.IdealSheafData)

/-- The closed immersion into the special fibre of a closed subscheme `Z ⊆ X` which contains the
special fibre scheme-theoretically. -/
def fibreSubschemeι (h : S.specialFiberIdeal ≤ Z) : Z.subscheme ⟶ S.specialFiber :=
  IsClosedImmersion.lift S.specialFiberι Z.subschemeι (by rwa [Z.ker_subschemeι])

/-- The closed immersion into the special fibre is compatible with the two inclusions into the
total space of the model. -/
theorem fibreSubschemeι_comp (h : S.specialFiberIdeal ≤ Z) :
    fibreSubschemeι S Z h ≫ S.specialFiberι = Z.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `fibreSubschemeι S Z h` from `Z` into the special fibre is a closed immersion. -/
instance isClosedImmersion_fibreSubschemeι (h : S.specialFiberIdeal ≤ Z) :
    IsClosedImmersion (fibreSubschemeι S Z h) := by
  have hcomp : IsClosedImmersion (fibreSubschemeι S Z h ≫ S.specialFiberι) := by
    rw [fibreSubschemeι_comp S Z h]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ S.specialFiberι

/-- The structure morphism over the residue field of a closed subscheme `Z ⊆ X` which contains
the special fibre scheme-theoretically. -/
def fibreSubschemeToSpec (h : S.specialFiberIdeal ≤ Z) : Z.subscheme ⟶ Spec (.of S.k) :=
  fibreSubschemeι S Z h ≫ S.specialFiberToSpec

/-- A closed subscheme `Z ⊆ X` that contains the special fibre is proper over the residue field. -/
instance isProper_fibreSubschemeToSpec (h : S.specialFiberIdeal ≤ Z) :
    IsProper (fibreSubschemeToSpec S Z h) := by
  rw [fibreSubschemeToSpec]
  infer_instance

/-- The structure morphism over the residue field lies over the structure morphism of the
model. -/
theorem fibreSubschemeToSpec_comp (h : S.specialFiberIdeal ≤ Z) :
    fibreSubschemeToSpec S Z h ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) =
      Z.subschemeι ≫ S.X_to_R := by
  rw [fibreSubschemeToSpec, Category.assoc, ← pullback.condition, ← Category.assoc,
    fibreSubschemeι_comp S Z h]

/-- The canonical homomorphism from the residue field to the global functions of a closed
subscheme `Z ⊆ X` which contains the special fibre scheme-theoretically. -/
def fibreSubschemeResidueMap (h : S.specialFiberIdeal ≤ Z) : S.k →+* Γ(Z.subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (fibreSubschemeToSpec S Z h).appTop).hom

/-- The canonical homomorphism from the base ring to the global functions of a closed subscheme
of the total space of the model. -/
def fibreSubschemeBaseMap : S.R →+* Γ(Z.subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.R)).inv ≫ (Z.subschemeι ≫ S.X_to_R).appTop).hom

/-- **The residue-field algebra structure is the one coming from the base ring.**  Composed with
the residue map `R ⟶ k`, the homomorphism `k ⟶ Γ(Z, 𝒪_Z)` is the canonical `R ⟶ Γ(Z, 𝒪_Z)`;
since `R ⟶ k` is surjective, this determines it uniquely. -/
theorem fibreSubschemeResidueMap_comp (h : S.specialFiberIdeal ≤ Z) :
    (fibreSubschemeResidueMap S Z h).comp (algebraMap S.R S.k) = fibreSubschemeBaseMap S Z := by
  have key : CommRingCat.ofHom (algebraMap S.R S.k) ≫ (Scheme.ΓSpecIso (.of S.k)).inv ≫
        (fibreSubschemeToSpec S Z h).appTop =
      (Scheme.ΓSpecIso (.of S.R)).inv ≫ (Z.subschemeι ≫ S.X_to_R).appTop := by
    rw [← fibreSubschemeToSpec_comp S Z h, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
  ext r
  exact congrArg (fun φ : CommRingCat.of S.R ⟶ Γ(Z.subscheme, ⊤) => φ.hom r) key

/-- The homomorphisms from the base ring are compatible with restriction along an inclusion of
closed subschemes. -/
theorem fibreSubschemeBaseMap_restrict {Z Z' : S.X.IdealSheafData} (hle : Z' ≤ Z) :
    (Scheme.IdealSheafData.inclusion hle).appTop.hom.comp (fibreSubschemeBaseMap S Z') =
      fibreSubschemeBaseMap S Z := by
  have key : (Scheme.ΓSpecIso (.of S.R)).inv ≫ (Z'.subschemeι ≫ S.X_to_R).appTop ≫
        (Scheme.IdealSheafData.inclusion hle).appTop =
      (Scheme.ΓSpecIso (.of S.R)).inv ≫ (Z.subschemeι ≫ S.X_to_R).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι hle]
  ext r
  exact congrArg (fun φ : CommRingCat.of S.R ⟶ Γ(Z.subscheme, ⊤) => φ.hom r) key

/-- The homomorphisms from the residue field are compatible with restriction along an inclusion
of closed subschemes which contain the special fibre scheme-theoretically. -/
theorem fibreSubschemeResidueMap_restrict {Z Z' : S.X.IdealSheafData}
    (h' : S.specialFiberIdeal ≤ Z') (hle : Z' ≤ Z) :
    (Scheme.IdealSheafData.inclusion hle).appTop.hom.comp (fibreSubschemeResidueMap S Z' h') =
      fibreSubschemeResidueMap S Z (h'.trans hle) := by
  ext z
  obtain ⟨r, rfl⟩ := S.surjective_algebraMap_residueField z
  have h1 := RingHom.congr_fun (fibreSubschemeResidueMap_comp S Z' h') r
  have h2 := RingHom.congr_fun (fibreSubschemeResidueMap_comp S Z (h'.trans hle)) r
  have h3 := RingHom.congr_fun (fibreSubschemeBaseMap_restrict S hle) r
  simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h3, h2]

end RegularProperModelSituation

open RegularProperModelSituation

/-! ### Radical sheaves of ideals and incomparability of the components -/

section Radical

variable {X : Scheme.{u}}

/-- **A reduced closed subscheme is cut out by a radical sheaf of ideals.**  A reduced closed
subscheme is the reduced induced structure on its own support, [Stacks, Tag 01J3], and that
structure is the radical. -/
theorem radical_eq_self_of_isReduced_subscheme (D : X.IdealSheafData) [IsReduced D.subscheme] :
    D.radical = D :=
  ((Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D D.support rfl).trans
    Scheme.IdealSheafData.vanishingIdeal_support).symm

/-- **Containment of supports reverses containment of radicals.**  The support and the vanishing
ideal form a Galois connection, and the vanishing ideal of the support is the radical. -/
theorem radical_le_radical_of_support_le {D E : X.IdealSheafData} (h : D.support ≤ E.support) :
    E.radical ≤ D.radical := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support (I := D),
    ← Scheme.IdealSheafData.vanishingIdeal_support (I := E)]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono h

/-- **The radical of a finite product of radical sheaves of ideals is their intersection**, the
sheaf-of-ideals form of `rad(IJ) = rad(I) ∩ rad(J)`. -/
theorem radical_prod {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData)
    (hrad : ∀ i ∈ s, (C i).radical = C i) : (∏ i ∈ s, C i).radical = s.inf C := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Finset.inf_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.radical_top]
  | cons i s hi ih =>
      rw [Finset.prod_cons, Scheme.IdealSheafData.radical_mul,
        hrad i (Finset.mem_cons_self ..), ih fun j hj => hrad j (Finset.mem_cons_of_mem hj),
        Finset.inf_cons]

/-- **A finite product of sheaves of ideals is contained in each of its factors**, hence in their
intersection. -/
theorem prod_le_inf {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData) :
    (∏ i ∈ s, C i) ≤ s.inf C := by
  classical
  refine Finset.le_inf fun i hi => ?_
  rw [← Finset.mul_prod_erase s C hi]
  exact Scheme.IdealSheafData.mul_le_left _ _

/-- **The sheaf of ideals of an effective Cartier divisor has a nonzero stalk at every point**:
it is generated there by a nonzerodivisor, which is nonzero because the local ring is not the
zero ring. -/
theorem stalk_ne_bot_of_isEffectiveCartierDivisor [IsIntegral X] {D : X.IdealSheafData}
    (hD : IsEffectiveCartierDivisor D) (x : X) :
    IdealSheafData.stalk D x ≠ ⊥ := by
  obtain ⟨f, hspan, hreg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hD x
  rw [hspan, Ne, Ideal.span_singleton_eq_bot]
  intro hf
  exact zero_notMem_nonZeroDivisors (hf ▸ hreg)

/-- Every point of a closed subscheme maps into the support of its sheaf of ideals. -/
private theorem subschemeι_mem_support (D : X.IdealSheafData) (z : D.subscheme) :
    D.subschemeι z ∈ D.support := by
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- **An effective Cartier divisor is not absorbed by a sheaf of ideals vanishing at a point**:
if `x ∈ V(D)` then `D · Q ≠ Q`, by Nakayama's lemma in the local ring at `x`. -/
private theorem mul_ne_self_of_isEffectiveCartierDivisor [IsIntegral X] {D Q : X.IdealSheafData}
    (hQ : IsEffectiveCartierDivisor Q) {x : X} (hx : x ∈ D.support) : D * Q ≠ Q := by
  intro hQeq
  obtain ⟨f, hspan, -⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hQ x
  have hstalk : IdealSheafData.stalk Q x =
      IdealSheafData.stalk D x * IdealSheafData.stalk Q x := by
    rw [← IdealSheafData.stalk_mul, hQeq]
  have hmax : IdealSheafData.stalk D x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IdealSheafData.stalk_le_maximalIdeal_iff_mem_support D x).2 hx
  have hjac : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hsmul : IdealSheafData.stalk Q x ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) • IdealSheafData.stalk Q x := by
    rw [Ideal.smul_eq_mul]
    exact hstalk.le.trans (Ideal.mul_mono_left hmax)
  have hfg : (IdealSheafData.stalk Q x).FG := by
    rw [hspan]
    exact ⟨{f}, by simp⟩
  exact stalk_ne_bot_of_isEffectiveCartierDivisor hQ x
    (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hsmul hjac)

/-- **Distinct components of a decomposition of the special fibre into integral divisors are
incomparable.**  If `X_k` has reduced structure `Σ Cᵢ`, with every `Cᵢ` an integral effective
Cartier divisor, then no `Cᵢ` is contained in another.

A containment `Cᵢ ⊆ Cⱼ` would make the index `i` redundant in the intersection `⋂ Cₗ`, which the
radicality of `Σ Cₗ` identifies with the product `∏ Cₗ`; the product over the remaining indices
would then satisfy `Q = Cᵢ · Q`, and Nakayama's lemma at a point of `Cᵢ` forces the stalk of `Q`
there to vanish, which the local equation of the effective Cartier divisor `Q` forbids. -/
theorem not_supportSet_subset_of_radical_eq_prod [IsIntegral X] {ι : Type*} (s : Finset ι)
    (C : ι → X.IdealSheafData) (I : X.IdealSheafData)
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hint : ∀ i ∈ s, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hred : I.radical = ∏ i ∈ s, C i) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ¬ (C i).supportSet ⊆ (C j).supportSet := by
  classical
  intro hsub
  -- every component is cut out by a radical sheaf of ideals
  have hrad : ∀ l ∈ s, (C l).radical = C l := fun l hl =>
    have := hint l hl
    have : IsReduced (C l).subscheme := inferInstance
    radical_eq_self_of_isReduced_subscheme (C l)
  -- the product of the components is radical, hence equal to their intersection
  have hprodrad : (∏ l ∈ s, C l).radical = ∏ l ∈ s, C l := by
    rw [← hred]
    exact Scheme.IdealSheafData.ext (funext fun U => Ideal.radical_idem _)
  have hinf : (∏ l ∈ s, C l) = s.inf C := hprodrad.symm.trans (radical_prod s C hrad)
  -- the `i`-th factor is redundant in the intersection
  have hCji : C j ≤ C i := by
    have h := radical_le_radical_of_support_le
      (D := C i) (E := C j) (by exact hsub)
    rwa [hrad i hi, hrad j hj] at h
  have herase : s.inf C = (s.erase i).inf C :=
    le_antisymm (Finset.le_inf fun l hl => Finset.inf_le (Finset.mem_of_mem_erase hl))
      (Finset.le_inf fun l hl => by
        by_cases hli : l = i
        · subst hli
          exact (Finset.inf_le (Finset.mem_erase.2 ⟨hij.symm, hj⟩)).trans hCji
        · exact Finset.inf_le (Finset.mem_erase.2 ⟨hli, hl⟩))
  -- the product over the remaining indices absorbs the `i`-th factor
  set Q : X.IdealSheafData := ∏ l ∈ s.erase i, C l with hQ
  have hsplit : (∏ l ∈ s, C l) = C i * Q := by
    rw [hQ, ← Finset.mul_prod_erase s C hi]
  have hQle : Q ≤ C i * Q := by
    rw [← hsplit, hinf, herase, hQ]
    exact prod_le_inf (s.erase i) C
  have hQeq : C i * Q = Q :=
    le_antisymm (Scheme.IdealSheafData.mul_le_right _ _) hQle
  -- Nakayama's lemma at a point of the `i`-th component
  obtain ⟨z⟩ : Nonempty (C i).subscheme := have := hint i hi; inferInstance
  have hQcart : IsEffectiveCartierDivisor Q := by
    simpa only [pow_one] using isEffectiveCartierDivisor_prod (s.erase i) C (fun _ => 1)
      (fun l hl => hC l (Finset.mem_of_mem_erase hl))
  exact mul_ne_self_of_isEffectiveCartierDivisor hQcart (subschemeι_mem_support _ z) hQeq

/-- **The support of a finite product of sheaves of ideals is the union of their supports.** -/
theorem coe_support_prod {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData) :
    ((∏ i ∈ s, C i).support : Set X) = ⋃ i ∈ s, ((C i).support : Set X) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.support_top]
      simp
  | cons i s hi ih =>
      rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul]
      simp only [Finset.set_biUnion_insert, Finset.cons_eq_insert, ← ih]
      rfl

/-- The support of a closed subscheme with integral — hence nonempty — structure is
nonempty. -/
theorem supportSet_nonempty_of_isIntegral_subscheme (D : X.IdealSheafData)
    (hD : AlgebraicGeometry.IsIntegral D.subscheme) : D.supportSet.Nonempty := by
  obtain ⟨z⟩ : Nonempty D.subscheme := inferInstance
  exact ⟨D.subschemeι z, (Scheme.IdealSheafData.mem_supportSet_iff_mem_support ..).2
    (subschemeι_mem_support D z)⟩

/-- **The greatest common divisor of a family over a finite set, read on the subtype of that
set**; the two divide each other. -/
theorem gcd_coe_sort {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    Finset.univ.gcd (fun x : {x // x ∈ s} => m x.1) = s.gcd m :=
  Nat.dvd_antisymm
    (Finset.dvd_gcd fun i hi =>
      Finset.gcd_dvd (f := fun x : {x // x ∈ s} => m x.1) (Finset.mem_univ ⟨i, hi⟩))
    (Finset.dvd_gcd fun x _ => Finset.gcd_dvd x.2)

end Radical

/-- **Each component of a decomposition `X_k = Σ mᵢCᵢ` with positive multiplicities contains the
special fibre scheme-theoretically**, so it carries a canonical structure morphism over the
residue field. -/
theorem specialFiberIdeal_le_of_mem (S : RegularProperModelSituation.{u}) {ι : Type*}
    (s : Finset ι) (C : ι → S.X.IdealSheafData) (m : ι → ℕ) (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) {i : ι} (hi : i ∈ s) :
    S.specialFiberIdeal ≤ C i := by
  classical
  have h1 : (∏ j ∈ s, C j ^ m j) ≤ ∏ j ∈ s, C j ^ (Pi.single i 1 : ι → ℕ) j :=
    prod_pow_le_prod_pow_of_le s C fun j hj => by
      by_cases hji : j = i
      · subst hji
        simp only [Pi.single_eq_same]
        exact hm j hj
      · simp [Pi.single_eq_of_ne hji]
  have h2 : (∏ j ∈ s, C j ^ (Pi.single i 1 : ι → ℕ) j) = C i := by
    rw [Finset.prod_eq_single_of_mem i hi fun j _ hj => by
      rw [Pi.single_eq_of_ne hj, pow_zero], Pi.single_eq_same, pow_one]
  exact hdec.trans_le (h1.trans_eq h2)

/-! ### The intersection matrix of a decomposition of the special fibre -/

section Matrix

variable (S : RegularProperModelSituation.{u}) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (C : ι → S.X.IdealSheafData)
  (hsfi : ∀ i, S.specialFiberIdeal ≤ C i)
  (hC : ∀ i, IsEffectiveCartierDivisor (C i))
  (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- **The intersection matrix of a decomposition of the special fibre**,
`(Cᵢ · Cⱼ) = deg(𝒪_X(Cⱼ)|_{Cᵢ})`, taken at the *canonical* structure morphism of each component
over the residue field, `Stacks.Models.RegularProperModelSituation.fibreSubschemeToSpec`.  Each
component contains the special fibre scheme-theoretically, so it has one; and they all factor
through the closed immersion of the special fibre, which is what makes the matrix symmetric. -/
def decompositionMatrix : ι → ι → ℤ := fun i j =>
  componentDegree S.k (C i) (fibreSubschemeToSpec S (C i) (hsfi i))
    (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i)
    (Stacks.Divisors.invertibleSheaf' (C j))
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _ (hC j))

/-- **The canonical structure morphisms over the residue field agree on the intersection of two
closed subschemes containing the special fibre**: both factor through the closed immersion of the
special fibre, which is a monomorphism. -/
theorem fibreSubschemeToSpec_comapCommIso (Z Z' : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ Z) (h' : S.specialFiberIdeal ≤ Z') :
    ((comapCommIso Z Z').hom ≫ (Z.comap Z'.subschemeι).subschemeι) ≫
        fibreSubschemeToSpec S Z' h' =
      (Z'.comap Z.subschemeι).subschemeι ≫ fibreSubschemeToSpec S Z h := by
  set p := (Z'.comap Z.subschemeι).subschemeι
  set q := (comapCommIso Z Z').hom ≫ (Z.comap Z'.subschemeι).subschemeι
  have h3 : (p ≫ fibreSubschemeι S Z h) ≫ S.specialFiberι =
      (q ≫ fibreSubschemeι S Z' h') ≫ S.specialFiberι := by
    rw [Category.assoc, Category.assoc, fibreSubschemeι_comp S Z h,
      fibreSubschemeι_comp S Z' h']
    exact comapCommIso_compat Z Z'
  have h4 : p ≫ fibreSubschemeι S Z h = q ≫ fibreSubschemeι S Z' h' :=
    (cancel_mono S.specialFiberι).mp h3
  show q ≫ (fibreSubschemeι S Z' h' ≫ S.specialFiberToSpec) =
    p ≫ (fibreSubschemeι S Z h ≫ S.specialFiberToSpec)
  rw [← Category.assoc, ← Category.assoc, h4]

omit [Fintype ι] [DecidableEq ι] in
/-- **Stacks Project, Tag 0C64 at a decomposition of the special fibre**: the intersection matrix
is symmetric.  For `i = j` the two sides are the same expression; for `i ≠ j` both are the
dimension over `k` of `H⁰` of the scheme-theoretic intersection `Cᵢ ∩ Cⱼ`, by the second
assertion of [Stacks, Tag 0AYY], and the intersection does not depend on which component it is
formed inside. -/
theorem decompositionMatrix_comm (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hdist : ∀ i j, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet) (i j : ι) :
    decompositionMatrix S C hsfi hC hdim i j = decompositionMatrix S C hsfi hC hdim j i := by
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · have key : ∀ {i j : ι}, i ≠ j → decompositionMatrix S C hsfi hC hdim i j = _ :=
      fun {i j} hne => by
      have := hC j
      exact componentDegree_invertibleSheaf_eq_finrank S.k (C i) (C j)
        (fibreSubschemeToSpec S (C i) (hsfi i))
        (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i) (hint i)
        fun hle => hdist i j hne (Scheme.IdealSheafData.support_antitone hle)
    rw [key hne, key hne.symm]
    exact congrArg _ (finrank_cohomologyOverField_comap_comm (C i) (C j) S.k
      (fibreSubschemeToSpec S (C i) (hsfi i)) (fibreSubschemeToSpec S (C j) (hsfi j))
      (fibreSubschemeToSpec_comapCommIso S (C i) (C j) (hsfi i) (hsfi j)))

omit [Fintype ι] [DecidableEq ι] in
/-- **Stacks Project, Tag 0C66, part (1), at a decomposition of the special fibre**: for `i ≠ j`
the entry `(Cᵢ · Cⱼ)` is nonnegative, and it vanishes exactly when the two components are
disjoint.  The canonical section of `𝒪_X(Cⱼ)` restricts to a nonzero section on the integral
proper curve `Cᵢ`, with zero scheme the intersection `Cᵢ ∩ Cⱼ`; parts (1) and (2) of
[Stacks, Tag 0B40] give the two assertions. -/
theorem decompositionMatrix_nonneg_and_eq_zero_iff
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hdist : ∀ i j, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet) {i j : ι} (hij : i ≠ j) :
    0 ≤ decompositionMatrix S C hsfi hC hdim i j ∧
      (decompositionMatrix S C hsfi hC hdim i j = 0 ↔
        (C i).supportSet ∩ (C j).supportSet = ∅) := by
  have := hint i
  have := hC j
  have hnn : 0 ≤ decompositionMatrix S C hsfi hC hdim i j :=
    componentDegree_invertibleSheaf_nonneg S.k (C i) (C j)
      (fibreSubschemeToSpec S (C i) (hsfi i))
      (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i) (hdist i j hij)
  have hpos : 0 < decompositionMatrix S C hsfi hC hdim i j ↔
      ((C i).supportSet ∩ (C j).supportSet).Nonempty :=
    componentDegree_invertibleSheaf_pos_iff S.k (C i) (C j)
      (fibreSubschemeToSpec S (C i) (hsfi i))
      (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i) (hdist i j hij)
  refine ⟨hnn, ?_⟩
  rw [← Set.not_nonempty_iff_eq_empty, ← hpos]
  omega

omit [DecidableEq ι] in
/-- **The bilinear expansion of the degree of a nonnegative combination of the components**,
`deg(𝒪_X(Σⱼ cⱼCⱼ)|_{Cᵢ}) = Σⱼ cⱼ (Cᵢ · Cⱼ)`, the invertible case of [Stacks, Tag 0AYX] at the
intersection matrix of a decomposition. -/
theorem decompositionMatrix_expand (c : ι → ℕ) (i : ι) :
    componentDegree S.k (C i) (fibreSubschemeToSpec S (C i) (hsfi i))
        (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (∏ j, C j ^ c j))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (isEffectiveCartierDivisor_prod Finset.univ C c fun j _ => hC j)) =
      ∑ j, (c j : ℤ) * decompositionMatrix S C hsfi hC hdim i j :=
  componentDegree_invertibleSheaf_prod S C (fun l => fibreSubschemeToSpec S (C l) (hsfi l))
    (fun l => isProper_fibreSubschemeToSpec S (C l) (hsfi l)) hdim i hC Finset.univ c _ _

omit [DecidableEq ι] in
/-- **The intersection matrix of a decomposition kills the multiplicity vector**,
`Σⱼ mⱼ(Cᵢ · Cⱼ) = 0`: the left-hand side is the expansion of `deg(𝒪_X(Σⱼ mⱼCⱼ)|_{Cᵢ})`, and that
sheaf is `𝒪_X(X_k)`, which is trivial because the special fibre is cut out by a uniformizer.  This
is part (2) of [Stacks, Tag 0C66] at the decomposition, read entry by entry. -/
theorem decompositionMatrix_mulVec_multiplicity (m : ι → ℕ)
    (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i) (i : ι) :
    ∑ j, (m j : ℤ) * decompositionMatrix S C hsfi hC hdim i j = 0 := by
  rw [← decompositionMatrix_expand S C hsfi hC hdim m i]
  exact componentDegree_divisorSheaf_specialFiber_eq_zero S Finset.univ C
    (fun l => fibreSubschemeToSpec S (C l) (hsfi l))
    (fun l => isProper_fibreSubschemeToSpec S (C l) (hsfi l)) hdim m i
    (fun j _ => hC j) hdec

omit [DecidableEq ι] in
/-- **Stacks Project, Tag 0C66, part (3), at a decomposition of the special fibre**: there is no
nonempty proper set `I` of indices with `(Cᵢ · Cⱼ) = 0` for every `i ∈ I` and every `j ∉ I`.

By part (1) such an `I` would make every component indexed by `I` disjoint from every component
indexed outside `I`, splitting the support of the special fibre into two disjoint nonempty closed
sets — the components cover it because their sum is its reduction, and there are finitely many of
them.  That contradicts the connectedness of the special fibre, [Stacks, Tag 0C62]. -/
theorem decompositionMatrix_connected
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hdist : ∀ i j, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet)
    (hred : S.specialFiberIdeal.radical = ∏ i, C i)
    (I : Set ι) (hne : I.Nonempty) (hI : I ≠ Set.univ) :
    ¬ ∀ i ∈ I, ∀ j ∉ I, decompositionMatrix S C hsfi hC hdim i j = 0 := by
  classical
  intro hzero
  set T : Set S.X := S.specialFiberIdeal.supportSet with hT
  -- the support of the special fibre is connected
  have hconn : _root_.IsConnected T := by
    have := S.connectedSpace_subscheme_radical_specialFiberIdeal
    have hrange : Set.range S.specialFiberIdeal.radical.subschemeι = T := by
      rw [hT, Scheme.IdealSheafData.range_subschemeι]
      rfl
    exact hrange ▸ isConnected_range S.specialFiberIdeal.radical.subschemeι.continuous
  -- the components cover it
  have hcover : T = ⋃ i, (C i).supportSet := by
    have h1 : T = ((∏ i, C i).support : Set S.X) := by
      rw [hT, ← hred]
      rfl
    rw [h1, coe_support_prod]
    ext x
    simp
  have hsub : ∀ i, (C i).supportSet ⊆ T := fun i x hx => by
    rw [hcover]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  -- the two halves are closed
  have hclosed : ∀ J : Set ι, IsClosed (⋃ i ∈ J, (C i).supportSet) := fun J =>
    (Set.toFinite J).isClosed_biUnion fun i _ => (C i).support.isClosed
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ I := by simpa [Set.eq_univ_iff_forall] using hI
  obtain ⟨x, -, hxA, hxB⟩ := isPreconnected_closed_iff.1 hconn.isPreconnected _ _
    (hclosed I) (hclosed Iᶜ)
    (by
      rw [hcover]
      refine Set.iUnion_subset fun i x hx => ?_
      by_cases hiI : i ∈ I
      · exact Or.inl (Set.mem_iUnion₂.2 ⟨i, hiI, hx⟩)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, hiI, hx⟩))
    (by
      obtain ⟨y, hy⟩ := supportSet_nonempty_of_isIntegral_subscheme (C i₀) (hint i₀)
      exact ⟨y, hsub i₀ hy, Set.mem_iUnion₂.2 ⟨i₀, hi₀, hy⟩⟩)
    (by
      obtain ⟨y, hy⟩ := supportSet_nonempty_of_isIntegral_subscheme (C j₀) (hint j₀)
      exact ⟨y, hsub j₀ hy, Set.mem_iUnion₂.2 ⟨j₀, hj₀, hy⟩⟩)
  obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.1 hxA
  obtain ⟨j, hjI, hxj⟩ := Set.mem_iUnion₂.1 hxB
  have hij : i ≠ j := fun e => hjI (e ▸ hiI)
  have h0 := ((decompositionMatrix_nonneg_and_eq_zero_iff S C hsfi hC hdim hint hdist
    hij).2).1 (hzero i hiI j hjI)
  exact (Set.eq_empty_iff_forall_notMem.1 h0) x ⟨hxi, hxj⟩

omit [DecidableEq ι] in
/-- **Stacks Project, Tag 0C66, part (4), at a decomposition of the special fibre.**  For every
rational coefficient family `x` the quadratic form of the intersection matrix is nonpositive, and
it vanishes exactly on the rational multiples of the multiplicity vector.

This is the source's own deduction from the other three parts through the linear algebra of
[Stacks, Tag 0C5X]: the matrix is symmetric, has nonnegative off-diagonal entries, kills the
strictly positive multiplicity vector and is irreducible. -/
@[sga "7 X 1.8" "special case"]
theorem decompositionForm_nonpos_and_eq_zero_iff (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hdist : ∀ i j, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet)
    (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i, C i) (x : ι → ℚ) :
    ∑ i, ∑ j, x i * x j * (decompositionMatrix S C hsfi hC hdim i j : ℚ) ≤ 0 ∧
      (∑ i, ∑ j, x i * x j * (decompositionMatrix S C hsfi hC hdim i j : ℚ) = 0 ↔
        ∃ q : ℚ, ∀ i, x i = q * (m i : ℚ)) :=
  ⟨intersectionForm_nonpos_of_properties (decompositionMatrix S C hsfi hC hdim) m
      (fun _ _ hij => (decompositionMatrix_nonneg_and_eq_zero_iff S C hsfi hC hdim hint
        hdist hij).1)
      (decompositionMatrix_comm S C hsfi hC hdim hint hdist) hm
      (decompositionMatrix_mulVec_multiplicity S C hsfi hC hdim m hdec) x,
    intersectionForm_eq_zero_iff_of_properties (decompositionMatrix S C hsfi hC hdim) m
      (fun _ _ hij => (decompositionMatrix_nonneg_and_eq_zero_iff S C hsfi hC hdim hint
        hdist hij).1)
      (decompositionMatrix_comm S C hsfi hC hdim hint hdist) hm
      (decompositionMatrix_mulVec_multiplicity S C hsfi hC hdim m hdec)
      (decompositionMatrix_connected S C hsfi hC hdim hint hdist hred) x⟩

/-- Each `mᵢ` is `d` times `mᵢ / d` over `ℤ`, for `d = gcd m`. -/
private theorem natCast_eq_gcd_mul_div {ι : Type*} [Fintype ι] (m : ι → ℕ) {d : ℕ}
    (hd : Finset.univ.gcd m = d) (i : ι) : (m i : ℤ) = d * ((m i / d : ℕ) : ℤ) := by
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (hd ▸ Finset.gcd_dvd (Finset.mem_univ i) : d ∣ m i)]

private theorem not_exists_rat_mul_of_add_eq_div_gcd {ι : Type*} [Fintype ι] (m a e : ι → ℕ)
    {d : ℕ} (hd : Finset.univ.gcd m = d) (hae : ∀ i, a i + e i = m i / d)
    (ha1 : ∀ i, 0 < a i) {i₀ : ι} (hi₀ : a i₀ < m i₀ / d) :
    ¬ ∃ q : ℚ, ∀ i, (e i : ℚ) = q * (m i : ℚ) := by
  rintro ⟨q, hq⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hi₀
  have hd0 : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hdpos.ne'
  have hmuZ := natCast_eq_gcd_mul_div m hd
  obtain ⟨l, hl⟩ := exists_gcd_mul_eq_mul Finset.univ m (fun i => (e i : ℤ)) q
    fun i _ => by push_cast; exact hq i
  have hlu : ∀ i, (e i : ℤ) = l * ((m i / d : ℕ) : ℤ) := fun i => by
    have h1 := hl i (Finset.mem_univ i)
    rw [hd, hmuZ i] at h1
    refine mul_left_cancel₀ hd0 (h1.trans ?_)
    ring
  have hae₀ := hae i₀
  have ha₀ := ha1 i₀
  have he₀ : 0 < e i₀ := by omega
  have hu₀ : (1 : ℤ) ≤ ((m i₀ / d : ℕ) : ℤ) := by omega
  have hl1 : 1 ≤ l := by
    by_contra hcon
    have hle : (e i₀ : ℤ) ≤ 0 := by
      rw [hlu i₀]
      exact mul_nonpos_of_nonpos_of_nonneg (by omega) (Int.natCast_nonneg _)
    omega
  have hlb : ((m i₀ / d : ℕ) : ℤ) ≤ (e i₀ : ℤ) := by
    rw [hlu i₀]
    nlinarith
  omega

private theorem exists_pos_sum_of_form_neg {ι : Type*} [Fintype ι] (N : ι → ι → ℤ)
    (u a e : ι → ℕ) (hae : ∀ i, (u i : ℤ) = a i + e i)
    (hker : ∀ i, ∑ j, (u j : ℤ) * N i j = 0)
    (hneg : ∑ i, ∑ j, (e i : ℤ) * (e j : ℤ) * N i j < 0) :
    ∃ i, 0 < e i ∧ 0 < ∑ j, (a j : ℤ) * N i j := by
  have hPE : ∀ i, ∑ j, (a j : ℤ) * N i j = -∑ j, (e j : ℤ) * N i j := by
    intro i
    have hsum : (∑ j, (a j : ℤ) * N i j) + ∑ j, (e j : ℤ) * N i j = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hker i)
      rw [hae j]
      ring
    linarith
  have hstep : ∀ i, (e i : ℤ) * (∑ j, (a j : ℤ) * N i j) =
      -∑ j, (e i : ℤ) * (e j : ℤ) * N i j := by
    intro i
    rw [hPE i, mul_neg, Finset.mul_sum]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm)
  have hsumpos : (0 : ℤ) < ∑ i, (e i : ℤ) * ∑ j, (a j : ℤ) * N i j := by
    have hrw : (∑ i, (e i : ℤ) * ∑ j, (a j : ℤ) * N i j) =
        -∑ i, ∑ j, (e i : ℤ) * (e j : ℤ) * N i j :=
      (Finset.sum_congr rfl fun i _ => hstep i).trans (Finset.sum_neg_distrib _)
    rw [hrw]
    omega
  obtain ⟨i, -, hipos⟩ := Finset.exists_lt_of_sum_lt
    (f := fun _ : ι => (0 : ℤ)) (g := fun i => (e i : ℤ) * ∑ j, (a j : ℤ) * N i j)
    (by simpa using hsumpos)
  refine ⟨i, ?_, pos_of_mul_pos_right hipos (Int.natCast_nonneg _)⟩
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hipos

/-- **The arithmetic of the induction step of [Stacks, Tag 0C68].**  Let `N` be a symmetric
intersection matrix which kills a strictly positive multiplicity vector `m` and whose quadratic
form over the rationals is nonpositive with nullspace exactly the line `ℚ·m` — that is, the
content of parts (2) and (4) of [Stacks, Tag 0C66].  Let `a` be a family of integers with
`1 ≤ aᵢ ≤ mᵢ/d`, `d = gcd(mᵢ)`, which is not everywhere equal to `mᵢ/d`.  Then some index `i` with
`aᵢ < mᵢ/d` has `Σⱼ aⱼ Nᵢⱼ > 0`.

Writing `eᵢ = mᵢ/d - aᵢ`, the family `e` is nonnegative and not everywhere zero, and it is not a
rational multiple of `m`:  a relation `eᵢ = q mᵢ` becomes `d eᵢ = l mᵢ`, hence `eᵢ = l (mᵢ/d)`,
with `l` an integer, by the Bézout computation `Stacks.Models.exists_gcd_mul_eq_mul`, and
`0 < eᵢ ≤ mᵢ/d - 1` leaves no room for such an `l`.  The form is therefore *strictly* negative at
`e`.  Since `N` kills `m` it kills `m/d`, so `Σⱼ aⱼ Nᵢⱼ = -Σⱼ eⱼ Nᵢⱼ` for every `i`, whence
`Σᵢ eᵢ Σⱼ aⱼ Nᵢⱼ = -Σᵢ Σⱼ eᵢ eⱼ Nᵢⱼ > 0`;  one summand is then positive, and both of its factors
must be. -/
private theorem exists_pos_sum_of_lt_div_gcd {ι : Type*} [Fintype ι] (N : ι → ι → ℤ)
    (m a : ι → ℕ) (_hm : ∀ i, 0 < m i)
    (hker : ∀ i, ∑ j, (m j : ℤ) * N i j = 0)
    (hform : ∀ x : ι → ℚ, ∑ i, ∑ j, x i * x j * (N i j : ℚ) ≤ 0 ∧
      (∑ i, ∑ j, x i * x j * (N i j : ℚ) = 0 ↔ ∃ q : ℚ, ∀ i, x i = q * (m i : ℚ)))
    (ha1 : ∀ i, 0 < a i) (ha2 : ∀ i, a i ≤ m i / Finset.univ.gcd m)
    (hlt : ∃ i, a i < m i / Finset.univ.gcd m) :
    ∃ i, a i < m i / Finset.univ.gcd m ∧ 0 < ∑ j, (a j : ℤ) * N i j := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, Finset.univ.gcd m = d := ⟨_, rfl⟩
  rw [hd] at ha2 hlt ⊢
  obtain ⟨i₀, hi₀⟩ := hlt
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hi₀
  have hd0 : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hdpos.ne'
  have hmuZ := natCast_eq_gcd_mul_div m hd
  set e : ι → ℕ := fun i => m i / d - a i with he
  have hae : ∀ i, a i + e i = m i / d := fun i => by
    have := ha2 i
    simp only [he]
    omega
  have haeZ : ∀ i, ((m i / d : ℕ) : ℤ) = (a i : ℤ) + (e i : ℤ) := fun i => by
    rw [← hae i]
    push_cast
    ring
  have hkeru : ∀ i, ∑ j, ((m j / d : ℕ) : ℤ) * N i j = 0 := by
    intro i
    have hmul : (d : ℤ) * ∑ j, ((m j / d : ℕ) : ℤ) * N i j = 0 := by
      rw [Finset.mul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hker i)
      rw [hmuZ j]
      ring
    exact (mul_eq_zero.mp hmul).resolve_left hd0
  have h4 := hform fun i => (e i : ℚ)
  have hne0 : ∑ i, ∑ j, (e i : ℚ) * (e j : ℚ) * (N i j : ℚ) ≠ 0 := fun h0 =>
    not_exists_rat_mul_of_add_eq_div_gcd m a e hd hae ha1 hi₀ (h4.2.1 h0)
  have hFneg : (∑ i, ∑ j, (e i : ℤ) * (e j : ℤ) * N i j) < 0 := by
    have hcast : ((∑ i, ∑ j, (e i : ℤ) * (e j : ℤ) * N i j : ℤ) : ℚ) =
        ∑ i, ∑ j, (e i : ℚ) * (e j : ℚ) * (N i j : ℚ) := by push_cast; ring
    have hQ : ((∑ i, ∑ j, (e i : ℤ) * (e j : ℤ) * N i j : ℤ) : ℚ) < 0 := by
      rw [hcast]
      exact lt_of_le_of_ne h4.1 hne0
    exact_mod_cast hQ
  obtain ⟨i, hi, hipos⟩ :=
    exists_pos_sum_of_form_neg N (fun i => m i / d) a e haeZ hkeru hFneg
  exact ⟨i, by have := hae i; omega, hipos⟩

omit [DecidableEq ι] in
include hC in
/-- **The geometric step of the induction of [Stacks, Tag 0C68].**  Let `X_k = Σ mᵢCᵢ` be a
decomposition of the special fibre into integral effective Cartier divisors whose reduction is
`Σ Cᵢ`, put `d = gcd(mᵢ)`, and let `a` be a family of integers with `1 ≤ aᵢ ≤ mᵢ/d` which is not
everywhere equal to `mᵢ/d`.  Then some index `i` with `aᵢ < mᵢ/d` has
`deg(𝒪_X(-Σⱼ aⱼCⱼ)|_{Cᵢ}) < 0`.

Parts (2) and (4) of [Stacks, Tag 0C66] at the decomposition feed
`Stacks.Models.exists_pos_sum_of_lt_div_gcd`, which produces an index `i` with `aᵢ < mᵢ/d` and
`Σⱼ aⱼ (Cᵢ · Cⱼ) > 0`.  The bilinear expansion reads that sum as `deg(𝒪_X(Σⱼ aⱼCⱼ)|_{Cᵢ})`, and
`deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})` is the invertible case of [Stacks, Tag 0AYX],
`Stacks.Models.componentDegreeAdditive`. -/
theorem exists_componentDegree_negativeTwist_neg (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hdist : ∀ i j, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet)
    (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i, C i)
    (a : ι → ℕ) (ha1 : ∀ i, 0 < a i) (ha2 : ∀ i, a i ≤ m i / Finset.univ.gcd m)
    (hlt : ∃ i, a i < m i / Finset.univ.gcd m)
    (D : S.X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hDa : D = ∏ j, C j ^ a j) :
    ∃ i, a i < m i / Finset.univ.gcd m ∧
      componentDegree S.k (C i) (fibreSubschemeToSpec S (C i) (hsfi i))
        (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i)
        (Stacks.Divisors.negativeTwist' D)
        (@Stacks.Divisors.isTensorInvertible_negativeTwist _ _ hD) < 0 := by
  subst hDa
  obtain ⟨i, hilt, hipos⟩ := exists_pos_sum_of_lt_div_gcd
    (decompositionMatrix S C hsfi hC hdim) m a hm
    (decompositionMatrix_mulVec_multiplicity S C hsfi hC hdim m hdec)
    (decompositionForm_nonpos_and_eq_zero_iff S C hsfi hC hdim m hm hint hdist hdec hred)
    ha1 ha2 hlt
  refine ⟨i, hilt, ?_⟩
  rw [componentDegree_negativeTwist_eq_neg S C (fun l => fibreSubschemeToSpec S (C l) (hsfi l))
    (fun l => isProper_fibreSubschemeToSpec S (C l) (hsfi l)) hdim i (∏ j, C j ^ a j) hD]
  have hexp : componentDegree S.k (C i) (fibreSubschemeToSpec S (C i) (hsfi i))
      (isProper_fibreSubschemeToSpec S (C i) (hsfi i)) (hdim i)
      (Stacks.Divisors.invertibleSheaf' (∏ j, C j ^ a j))
      (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _ hD) =
        ∑ j, (a j : ℤ) * decompositionMatrix S C hsfi hC hdim i j :=
    decompositionMatrix_expand S C hsfi hC hdim a i
  omega

end Matrix

/-! ### One step of the filtration: adding a component of positive intersection -/

/-- **An invertible module of negative degree on an integral proper curve has no nonzero global
section**, applied to the restriction `𝒪_X(-D)|_C` of the sheaf of an effective Cartier divisor
`D ⊆ X` to a closed subscheme `C ⊆ X` which is an integral proper curve over the field `k`.  This
is part (1) of [Stacks, Tag 0B40] read contrapositively: a nonzero global section of an invertible
module on such a curve has a zero scheme finite over `k`, whose length is the degree, so the
degree is nonnegative.  The sections are those of the push-forward along the closed immersion of
`C`, which over the whole space are the sections of the restriction itself.

Finite dimensionality of the cohomology of the structure sheaf of `C`, [Stacks, Tag 02O6], is the
one input that part of Tag 0B40 needs; it is discharged inside
`AlgebraicGeometry.invertibleCurveDegree_nonneg_of_eval_top_ne_zero`, so no such hypothesis
appears here. -/
theorem forall_eq_zero_of_componentDegree_neg (k : Type u) [Field k] {X : Scheme.{u}}
    (D C : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (gC : C.subscheme ⟶ Spec (.of k)) (hgC : IsProper gC)
    (hdimC : topologicalKrullDim C.subscheme ≤ 1)
    (hintC : AlgebraicGeometry.IsIntegral C.subscheme)
    (hneg : componentDegree k C gC hgC hdimC (negativeTwist D)
      (@stacksIsInvertible_negativeTwist _ D hD) < 0)
    (y : Γ((Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), ⊤)) :
    y = 0 := by
  by_contra hy
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible C.subscheme.sheaf.obj
      C.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) :=
    isInvertible_restrict C (negativeTwist D) (@stacksIsInvertible_negativeTwist _ D hD)
  have heval := Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top
    ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) y
  have hnonneg := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k gC hdimC
    ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf _ y)
    (fun hcon => hy (heval.symm.trans hcon))
  exact absurd hnonneg (not_le.mpr hneg)

/-- **Adding a component to a divisor is injective on global functions once the complementary
twist has no sections.**  For effective Cartier divisors `D` and `C` on `X`, the sequence
`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{D + C} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T] is exact, and taking sections over
the whole space is left exact, so the restriction `Γ(D + C, 𝒪) ⟶ Γ(D, 𝒪)` is injective as soon as
`𝒪_X(-D)|_C` has no nonzero global section. -/
@[sga "7 X 1.13" "partial"]
theorem injective_inclusion_appTop_of_forall_eq_zero {X : Scheme.{u}}
    (D C : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hDC : IsEffectiveCartierDivisor (D * C)) (hC : IsEffectiveCartierDivisor C)
    (hvanish : ∀ y : Γ((Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), ⊤), y = 0)
    (hle : D * C ≤ D) :
    Function.Injective (Scheme.IdealSheafData.inclusion hle).appTop.hom := by
  obtain ⟨f, hzero, hSE⟩ := addEffectiveCartierDivisor_shortExact D (D * C) C hD hDC hC hle rfl
  have hinj : Function.Injective
      ((Scheme.IdealSheafData.closedSubschemeRestriction hle).app ⊤) := by
    intro u v huv
    have h0 : (Scheme.IdealSheafData.closedSubschemeRestriction hle).app ⊤ (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    obtain ⟨y, hy⟩ := Stacks.Algebraization.exists_app_eq_of_shortExact _ hSE ⊤ (u - v) h0
    rw [hvanish y, map_zero] at hy
    exact sub_eq_zero.mp hy.symm
  intro a b hab
  exact hinj ((Scheme.IdealSheafData.closedSubschemeRestriction_app_top hle a).trans
    (hab.trans (Scheme.IdealSheafData.closedSubschemeRestriction_app_top hle b).symm))

/-! ### Tag 0C68 -/

section Filtration

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ)

/-- The two assertions made about each stage of the filtration: that its global functions form a
field, and that they are finite over the residue field for the canonical algebra structure. -/
private abbrev IsFieldFinite (Z : S.X.IdealSheafData) : Prop :=
  IsField Γ(Z.subscheme, ⊤) ∧
    ∀ h : S.specialFiberIdeal ≤ Z, (fibreSubschemeResidueMap S Z h).Finite

/-- Raising one coefficient `aᵢ < bᵢ` by one keeps `0 < a ≤ b` on `s` and lowers the total defect
`Σ (bⱼ - aⱼ)` by one. -/
private theorem exists_update_succ (b a : ι → ℕ) {n : ℕ} {i : ι} (hi : i ∈ s) (hlt : a i < b i)
    (ha1 : ∀ j ∈ s, 0 < a j) (ha2 : ∀ j ∈ s, a j ≤ b j) (hn : ∑ j ∈ s, (b j - a j) = n + 1) :
    ∃ a' : ι → ℕ, a' i = a i + 1 ∧ (∀ j, j ≠ i → a' j = a j) ∧ (∀ j ∈ s, 0 < a' j) ∧
      (∀ j ∈ s, a' j ≤ b j) ∧ ∑ j ∈ s, (b j - a' j) = n := by
  classical
  obtain ⟨a', ha'i, ha'ne⟩ : ∃ a' : ι → ℕ, a' i = a i + 1 ∧ ∀ j, j ≠ i → a' j = a j :=
    ⟨Function.update a i (a i + 1), Function.update_self .., fun _ hj =>
      Function.update_of_ne hj ..⟩
  refine ⟨a', ha'i, ha'ne, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · obtain rfl | hji := eq_or_ne j i
    · omega
    · simpa only [ha'ne j hji] using ha1 j hj
  · obtain rfl | hji := eq_or_ne j i
    · omega
    · simpa only [ha'ne j hji] using ha2 j hj
  have e1 : ∑ j ∈ s, (b j - a j) = (b i - a i) + ∑ j ∈ s.erase i, (b j - a j) :=
    (Finset.add_sum_erase s _ hi).symm
  have e2 : ∑ j ∈ s, (b j - a' j) = (b i - a' i) + ∑ j ∈ s.erase i, (b j - a' j) :=
    (Finset.add_sum_erase s _ hi).symm
  have e3 : ∑ j ∈ s.erase i, (b j - a' j) = ∑ j ∈ s.erase i, (b j - a j) :=
    Finset.sum_congr rfl fun j hj => by rw [ha'ne j (Finset.ne_of_mem_erase hj)]
  rw [e1] at hn
  rw [e2, e3, ha'i]
  omega

/-- Passing to a smaller closed subscheme `E ≤ D` containing the special fibre, along an injective
restriction of global functions, preserves `IsFieldFinite`. -/
private theorem isFieldFinite_of_le {D E : S.X.IdealSheafData} (hle : E ≤ D)
    (hsfi : S.specialFiberIdeal ≤ E)
    (hinj : Function.Injective (Scheme.IdealSheafData.inclusion hle).appTop.hom)
    (hff : IsFieldFinite S D) : IsFieldFinite S E := by
  obtain ⟨hfield, hfin⟩ := hff
  obtain ⟨hFA, hFB⟩ := isField_and_finite_of_injective S.k
    (fibreSubschemeResidueMap S _ hsfi) (fibreSubschemeResidueMap S _ (hsfi.trans hle))
    (Scheme.IdealSheafData.inclusion hle).appTop.hom
    (fibreSubschemeResidueMap_restrict S hsfi hle) hinj hfield (hfin _)
  exact ⟨hFA, fun _ => hFB⟩

/-- Adding a component `B` to an effective Cartier divisor `D`, when `𝒪_X(-D)|_B` has no nonzero
global section, preserves `IsFieldFinite`. -/
private theorem isFieldFinite_mul_of_forall_eq_zero {D B : S.X.IdealSheafData}
    (hD : IsEffectiveCartierDivisor D) (hDB : IsEffectiveCartierDivisor (D * B))
    (hB : IsEffectiveCartierDivisor B)
    (hvanish : ∀ y : Γ((Scheme.Modules.pushforward B.subschemeι).obj
      ((Scheme.Modules.pullback B.subschemeι).obj (negativeTwist D)), ⊤), y = 0)
    (hsfi : S.specialFiberIdeal ≤ D * B) (hff : IsFieldFinite S D) :
    IsFieldFinite S (D * B) :=
  isFieldFinite_of_le S (mul_le_left _ _) hsfi
    (injective_inclusion_appTop_of_forall_eq_zero D B hD hDB hB hvanish _) hff

/-- **The induction behind [Stacks, Tag 0C68]**, at the one geometric input it needs: that at
every stage short of `Σ (mᵢ/d)Cᵢ` some component `Cᵢ` still to be added carries no nonzero global
section of `𝒪_X(-Σⱼ aⱼCⱼ)|_{Cᵢ}`.  From a coefficient family `a` with `1 ≤ aᵢ ≤ mᵢ/d` whose total
defect is `n`, the divisor `Σ aᵢCᵢ` is then the bottom of a chain reaching `Σ (mᵢ/d)Cᵢ` by single
components, every stage of which is an effective Cartier divisor with field-valued global
functions finite over the residue field. -/
private theorem exists_chain_aux
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hvanish : ∀ a : ι → ℕ, (∀ i ∈ s, 0 < a i) → (∀ i ∈ s, a i ≤ m i / s.gcd m) →
      (∃ i ∈ s, a i < m i / s.gcd m) →
      ∃ i ∈ s, a i < m i / s.gcd m ∧
        ∀ y : Γ((Scheme.Modules.pushforward (C i).subschemeι).obj
          ((Scheme.Modules.pullback (C i).subschemeι).obj
            (negativeTwist (∏ j ∈ s, C j ^ a j))), ⊤), y = 0) :
    ∀ (n : ℕ) (a : ι → ℕ), (∀ i ∈ s, 0 < a i) → (∀ i ∈ s, a i ≤ m i / s.gcd m) →
      ∑ i ∈ s, (m i / s.gcd m - a i) = n → IsFieldFinite S (∏ j ∈ s, C j ^ a j) →
      ∃ (M : ℕ) (Z : ℕ → S.X.IdealSheafData),
        Z 0 = ∏ j ∈ s, C j ^ a j ∧ Z M = reducedSpecialFibre s C m ∧
        (∀ j < M, ∃ i ∈ s, Z (j + 1) = Z j * C i ∧ Z (j + 1) ≤ Z j) ∧
        ∀ j ≤ M, IsEffectiveCartierDivisor (Z j) ∧ S.specialFiberIdeal ≤ Z j ∧
          IsFieldFinite S (Z j) := by
  classical
  have hcart : ∀ a : ι → ℕ, IsEffectiveCartierDivisor (∏ j ∈ s, C j ^ a j) := fun a =>
    isEffectiveCartierDivisor_prod s C a hC
  have hsfi_le : ∀ a : ι → ℕ, (∀ i ∈ s, a i ≤ m i / s.gcd m) →
      S.specialFiberIdeal ≤ ∏ j ∈ s, C j ^ a j := fun a ha =>
    hdec.trans_le (prod_pow_le_prod_pow_of_le s C
      fun i hi => (ha i hi).trans (Nat.div_le_self _ _))
  intro n
  induction n with
  | zero =>
    intro a _ ha2 hn hff
    have hfull : ∀ i ∈ s, a i = m i / s.gcd m := fun i hi =>
      le_antisymm (ha2 i hi) (Nat.le_of_sub_eq_zero (Finset.sum_eq_zero_iff.mp hn i hi))
    have heq : (∏ j ∈ s, C j ^ a j) = reducedSpecialFibre s C m :=
      Finset.prod_congr rfl fun j hj => by rw [hfull j hj]
    exact ⟨0, fun _ => ∏ j ∈ s, C j ^ a j, rfl, heq,
      fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j _ => ⟨hcart a, hsfi_le a ha2, hff⟩⟩
  | succ n ih =>
    intro a ha1 ha2 hn hff
    have hexists : ∃ i ∈ s, a i < m i / s.gcd m := by
      by_contra! hcon
      rw [Finset.sum_eq_zero fun i hi => Nat.sub_eq_zero_of_le (hcon i hi)] at hn
      omega
    obtain ⟨i, hi, hlt, hzero⟩ := hvanish a ha1 ha2 hexists
    obtain ⟨a', ha'i, ha'ne, ha1', ha2', hsum⟩ :=
      exists_update_succ s (fun j => m j / s.gcd m) a hi hlt ha1 ha2 hn
    have hprod : (∏ j ∈ s, C j ^ a' j) = (∏ j ∈ s, C j ^ a j) * C i :=
      prod_pow_succ_at s C hi ha'i fun j _ hj => ha'ne j hj
    have hle : (∏ j ∈ s, C j ^ a j) * C i ≤ ∏ j ∈ s, C j ^ a j := mul_le_left _ _
    have hcart' : IsEffectiveCartierDivisor ((∏ j ∈ s, C j ^ a j) * C i) :=
      hprod ▸ hcart a'
    have hsfi' : S.specialFiberIdeal ≤ (∏ j ∈ s, C j ^ a j) * C i :=
      hprod ▸ hsfi_le a' ha2'
    have hff' : IsFieldFinite S (∏ j ∈ s, C j ^ a' j) := by
      rw [hprod]
      exact isFieldFinite_mul_of_forall_eq_zero S (hcart a) hcart'
        (hC i hi) hzero hsfi' hff
    obtain ⟨M, Z, hZ0, hZM, hsteps, hprops⟩ := ih a' ha1' ha2' hsum hff'
    let Z' : ℕ → S.X.IdealSheafData := fun
      | 0 => ∏ j ∈ s, C j ^ a j
      | t + 1 => Z t
    refine ⟨M + 1, Z', rfl, hZM, ?_, ?_⟩
    · rintro (_ | t) _
      · exact ⟨i, hi, hZ0.trans hprod, (hZ0.trans hprod).trans_le hle⟩
      · exact hsteps t (by omega)
    · rintro (_ | t) hj
      · exact ⟨hcart a, hsfi'.trans hle, hff⟩
      · exact hprops t (by omega)

/-- **The geometric step of [Stacks, Tag 0C68]**: at every coefficient family `0 < aᵢ ≤ mᵢ/d`
short of `mᵢ/d`, some component `Cᵢ` with `aᵢ < mᵢ/d` carries no nonzero global section of
`𝒪_X(-Σⱼ aⱼCⱼ)|_{Cᵢ}`. -/
private theorem exists_lt_forall_eq_zero_of_radical_eq_prod
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i ∈ s, C i)
    (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (a : ι → ℕ) (ha1 : ∀ i ∈ s, 0 < a i) (ha2 : ∀ i ∈ s, a i ≤ m i / s.gcd m)
    (hexists : ∃ i ∈ s, a i < m i / s.gcd m) :
    ∃ i ∈ s, a i < m i / s.gcd m ∧
      ∀ y : Γ((Scheme.Modules.pushforward (C i).subschemeι).obj
        ((Scheme.Modules.pullback (C i).subschemeι).obj
          (negativeTwist (∏ j ∈ s, C j ^ a j))), ⊤), y = 0 := by
  classical
  have hsfi : ∀ i ∈ s, S.specialFiberIdeal ≤ C i := fun i hi =>
    specialFiberIdeal_le_of_mem S s C m hm hdec hi
  have hXint : IsIntegral S.X := S.toRegularModelSituation.isIntegral_X
  have hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ (C i).supportSet ⊆ (C j).supportSet :=
    fun _ hi _ hj hij => not_supportSet_subset_of_radical_eq_prod s C S.specialFiberIdeal hC
      (fun l _ => hint l) hred hi hj hij
  have hgcd : Finset.univ.gcd (fun x : {x // x ∈ s} => m x.1) = s.gcd m := gcd_coe_sort s m
  have hdec' : S.specialFiberIdeal = ∏ x : {x // x ∈ s}, C x.1 ^ m x.1 :=
    hdec.trans (Finset.prod_coe_sort s fun i => C i ^ m i).symm
  have hred' : S.specialFiberIdeal.radical = ∏ x : {x // x ∈ s}, C x.1 :=
    hred.trans (Finset.prod_coe_sort s C).symm
  obtain ⟨i₀, hi₀, hi₀lt⟩ := hexists
  obtain ⟨x, hxlt, hxdeg⟩ := exists_componentDegree_negativeTwist_neg S
    (fun x : {x // x ∈ s} => C x.1) (fun x => hsfi x.1 x.2) (fun x => hC x.1 x.2)
    (fun x => hdim x.1) (fun x => m x.1) (fun x => hm x.1 x.2) (fun x => hint x.1)
    (fun x y hxy => hdist x.1 x.2 y.1 y.2 fun e => hxy (Subtype.ext e))
    hdec' hred' (fun x => a x.1) (fun x => ha1 x.1 x.2)
    (fun x => by simpa only [hgcd] using ha2 x.1 x.2)
    ⟨⟨i₀, hi₀⟩, by simpa only [hgcd] using hi₀lt⟩
    (∏ j ∈ s, C j ^ a j) (isEffectiveCartierDivisor_prod s C a hC)
    (Finset.prod_coe_sort s fun j => C j ^ a j).symm
  rw [hgcd] at hxlt
  exact ⟨x.1, x.2, hxlt, forall_eq_zero_of_componentDegree_neg S.k (∏ j ∈ s, C j ^ a j) (C x.1)
    (isEffectiveCartierDivisor_prod s C a hC)
    (fibreSubschemeToSpec S (C x.1) (hsfi x.1 x.2))
    (isProper_fibreSubschemeToSpec S (C x.1) (hsfi x.1 x.2)) (hdim x.1) (hint x.1)
    hxdeg⟩

/-- **Stacks Project, Tag 0C68** [Artin–Winters, Lemma 2.6].  In Situation
[Stacks, Tag 0C61], write the special fibre as a sum of effective Cartier divisors
`X_k = Σ mᵢCᵢ`, put `d = gcd(mᵢ)` and let `D = Σ (mᵢ/d)Cᵢ`.  Then there is a sequence of
effective Cartier divisors `(X_k)_red = Z₀ ⊆ Z₁ ⊆ … ⊆ Z_M = D` in which each step
`Z_{j+1} = Z_j + C_{i_j}` adds a single component, and such that `H⁰(Z_j, 𝒪_{Z_j})` is a field,
finite over the residue field `k` for the algebra structure induced by the base ring, for every
`j = 0, …, M`.

Every input of the source's induction is proved here.  Connectedness of the reduced special
fibre is [Stacks, Tag 0C62],
`Stacks.Models.RegularProperModelSituation.connectedSpace_subscheme_radical_specialFiberIdeal`;
finiteness of the global functions of a proper scheme over `k` is clause (1) of
[Stacks, Tag 0BUG],
`Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper`; finite
dimensionality of coherent cohomology over a field is [Stacks, Tag 02O6],
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_unit`; and the geometric step is
`Stacks.Models.exists_componentDegree_negativeTwist_neg`, which runs the four properties of
[Stacks, Tag 0C66] at the given decomposition.  [Stacks, Tag 0C4T] and part (1) of
[Stacks, Tag 0B40] enter through
`Stacks.Models.injective_inclusion_appTop_of_forall_eq_zero`.  See the implementation notes of
this file. -/
@[stacks 0C68 "the whole lemma: the increasing chain of effective Cartier divisors from the \
reduced special fibre (X_k)_red to the divisor D = sum (mᵢ/d)Cᵢ, d = gcd(mᵢ), each step adding a \
single component, with H⁰(Z_j, O_{Z_j}) a field finite over the residue field at every stage. \
Stated at a decomposition X_k = sum mᵢCᵢ of the special fibre into integral proper curves over \
the residue field, which is the opening phrase of Situation 0C61"]
theorem exists_chain_reducedSpecialFibre
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i ∈ s, C i)
    (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k)) (_hgproper : ∀ i, IsProper (g i))
    (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme) :
    ∃ (M : ℕ) (Z : ℕ → S.X.IdealSheafData),
      Z 0 = S.specialFiberIdeal.radical ∧ Z M = reducedSpecialFibre s C m ∧
      (∀ j < M, ∃ i ∈ s, Z (j + 1) = Z j * C i ∧ Z (j + 1) ≤ Z j) ∧
      ∀ j ≤ M, IsEffectiveCartierDivisor (Z j) ∧ IsField Γ((Z j).subscheme, ⊤) ∧
        ∃ φ : S.k →+* Γ((Z j).subscheme, ⊤),
          φ.comp (algebraMap S.R S.k) = fibreSubschemeBaseMap S (Z j) ∧ φ.Finite := by
  classical
  have hone : ∀ i ∈ s, (1 : ℕ) ≤ m i / s.gcd m := fun i hi => by
    have hdpos : 0 < s.gcd m :=
      Nat.pos_of_ne_zero fun h => (hm i hi).ne' (Finset.gcd_eq_zero_iff.mp h i hi)
    exact (Nat.one_le_div_iff hdpos).mpr (Nat.le_of_dvd (hm i hi) (Finset.gcd_dvd hi))
  have hZ0 : (∏ j ∈ s, C j ^ (fun _ => 1 : ι → ℕ) j) = S.specialFiberIdeal.radical := by
    simpa only [pow_one] using hred.symm
  have hsfi0 : S.specialFiberIdeal ≤ S.specialFiberIdeal.radical :=
    Scheme.IdealSheafData.le_radical _
  have hreduced : IsReduced S.specialFiberIdeal.radical.subscheme :=
    Scheme.IdealSheafData.vanishingIdeal_support (I := S.specialFiberIdeal) ▸
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal S.specialFiberIdeal.support
  -- the base case: Tag 0C62 and clause (1) of Tag 0BUG
  have hconnected : ConnectedSpace S.specialFiberIdeal.radical.subscheme :=
    S.connectedSpace_subscheme_radical_specialFiberIdeal
  have hff0 : IsFieldFinite S (∏ j ∈ s, C j ^ (fun _ => 1 : ι → ℕ) j) := by
    rw [hZ0]
    refine ⟨isField_globalSections_of_connectedSpace S.k
      (fibreSubschemeToSpec S _ hsfi0), fun h => ?_⟩
    exact @Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper
      S.k _ _ (fibreSubschemeToSpec S _ h) inferInstance
  -- the inductive step: the four properties of Tag 0C66 at the given decomposition
  obtain ⟨M, Z, h0, hM, hsteps, hprops⟩ :=
    exists_chain_aux S s C m hC hdec
      (exists_lt_forall_eq_zero_of_radical_eq_prod S s C m hC hm hdec hred hdim hint)
      (∑ i ∈ s, (m i / s.gcd m - 1)) (fun _ => 1)
      (fun _ _ => Nat.one_pos) hone rfl hff0
  refine ⟨M, Z, h0.trans hZ0, hM, hsteps, fun j hj => ?_⟩
  obtain ⟨hcart, hsfiZ, hfield, hfin⟩ := hprops j hj
  exact ⟨hcart, hfield, fibreSubschemeResidueMap S (Z j) hsfiZ,
    fibreSubschemeResidueMap_comp S (Z j) hsfiZ, hfin hsfiZ⟩

end Filtration

end Stacks.Models

end
