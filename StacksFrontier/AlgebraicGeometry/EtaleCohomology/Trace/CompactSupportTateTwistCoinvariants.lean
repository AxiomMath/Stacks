module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.CategoryTheory.Trace.Sorites.Coinvariants
import StacksCore.Tactic.StacksAttribute

/-!
# Degree-two compactly supported cohomology of a curve and the Tate-twisted coinvariants

Let `k` be a field, let `X/k` be a geometrically connected smooth curve, let `Λ` be a finite
ring with `#Λ ∈ k^*` and let `ρ : π₁(X, η̄) → Aut_Λ(M)` be a continuous representation on a
finite `Λ`-module `M`.  Étale Cohomology, Lemma 03VK identifies the degree-two compactly
supported cohomology of the geometric curve with the Tate twist by `-1` of the coinvariants of
the geometric fundamental group:

`H²_c(X_{k̄}, ℱ_ρ) = (M)_{π₁(X_{k̄}, η̄)}(-1)` as `Gal(k^{sep}/k)`-modules.

Both the Galois action on the right-hand side and the twist are constructed here.  The geometric
fundamental group sits inside the arithmetic one as a normal subgroup `N` with quotient the
absolute Galois group — the fundamental exact sequence opening the source's section — so the
`N`-coinvariants of a representation of `π₁(X, η̄)` carry a residual action of that quotient.
The twist is the one the source writes down: `σ ∈ Gal(k^{sep}/k)` acts by `χ_cycl(σ)⁻¹`
composed with `σ`, where `χ_cycl` is the cyclotomic character.

## Main definitions

* `Stacks.EtaleCohomology.centralScalar` — multiplication by an element of the central subring
  `ZMod n` of `Λ`, as a `Λ`-linear endomorphism of a `Λ`-module.
* `Stacks.EtaleCohomology.galoisRingEquivHom`, `Stacks.EtaleCohomology.galoisRootsOfUnity` and
  `Stacks.EtaleCohomology.cyclotomicCharacterModN` — the absolute Galois group acting by ring
  automorphisms and on the roots of unity, and the mod-`n` cyclotomic character of a separably
  closed extension.
* `Stacks.EtaleCohomology.normalCoinvariantsRepresentation`,
  `Stacks.EtaleCohomology.quotientCoinvariantsRepresentation` and
  `Stacks.EtaleCohomology.galoisCoinvariantsRepresentation` — the action of the ambient group on
  the coinvariants of a normal subgroup, its factorisation through the quotient group, and its
  transport along an identification of that quotient with the Galois group.
* `Stacks.EtaleCohomology.tateTwistNegOne` — the Tate twist by `-1` of a Galois module: the same
  `Λ`-module, with `σ` acting by `χ_cycl(σ)⁻¹` composed with `σ`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyTwo` — the degree-two compactly supported
  cohomology module of Tag 0GJZ at a sheaf placed in degree zero.

## Main results

* `Stacks.EtaleCohomology.tateTwistNegOne_apply` — the twisted action, unfolded.
* `Stacks.EtaleCohomology.galoisRootsOfUnity_eq_pow` — `σ` raises an `n`-th root of unity to the
  power `χ_cycl(σ)`, inside the group of `n`-th roots of unity.
* `Stacks.EtaleCohomology.eq_tateTwistNegOne_of_centralScalar_eq` — a map intertwining two
  actions up to the scalar `χ_cycl(σ)` is equivariant for the Tate twist by `-1`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyTwo_galoisIso_tateTwistCoinvariants` —
  Tag 03VK in its Galois-module form, from a nondegenerate equivariant `μ_n`-pairing.

## Implementation notes

Coinvariants are not redefined: `Stacks.Trace.coinvariantsKer`, `Stacks.Trace.coinvariants` and
`Stacks.Trace.coinvariantsMk` of Tag 03UD are used throughout.  Those are stated for an
arbitrary ring `Λ`, which matters here because the source's `Λ` is a finite ring and is not
assumed commutative; Mathlib's `Representation.Coinvariants` and its
`Representation.quotientToCoinvariants` are available only over a commutative coefficient ring,
so they cannot carry the statement.  What is added beside Tag 03UD's coinvariants is the
residual action of a quotient group on the coinvariants of a normal subgroup, which Tag 03UD's
module has only for its own extension `1 → G → Γ → ℕ → 1`.

The twist is the source's own definition and not a choice: the mod-`n` cyclotomic character is
Mathlib's `modularCyclotomicCharacter`, pinned by `modularCyclotomicCharacter.spec`, and the
scalar `χ_cycl(σ)⁻¹` acts through the structural map `ZMod n → Λ`, whose image is central, so
the twisted action is again by `Λ`-linear maps.  The hypothesis `#Λ ∈ k^*` of the source appears
as `[NeZero (n : ksep)]`, which together with separable closedness gives
`HasEnoughRootsOfUnity ksep n` and hence exactly `n` roots of unity; no primitive root is chosen.

Taking the geometric base to be a separable closure rather than an algebraic closure is the
source's own convention: the Galois group of the section is `Gal(k^{sep}/k)`.

Three hypotheses of the source are not imposed, which only strengthens the statement:
continuity of `ρ`, finiteness of `Λ` and of `M`, and the identification of `n` with `#Λ`.  None
of them is needed for the conclusion once the pairing is given, and the source uses them only to
produce `ℱ_ρ` and the pairing, which are hypotheses here.  What `n` is used for is the twist, and
there the requirement is exactly the source's: `n` invertible in `k`, so in `k^{sep}`.

The geometric input enters as a pairing with `μ_n` coefficients rather than as a bare
isomorphism.  This is where the source puts it too — the closing line of its proof attributes
the twist to the canonical identification `H²_c(X_{k̄}, μ_n) = ℤ/nℤ` — and it is what makes the
twist a conclusion rather than an assumption: the pairing is equivariant with no twist in sight,
and the twist is produced by computing the Galois action on `μ_n`.

### No unrestricted `@[stacks 03VK]`

Four inputs of the source are carried as explicit hypotheses, each because the library has no
statement to discharge it.

* **Tag 0DV5 part (1), that is Tag 03RV and hence Tag 0245.** The sheaf `ℱ_ρ` attached to `ρ`.
  Tag 0DV5 part (2) is
  `Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`, which carries
  part (1) as a hypothesis and is for abelian rather than `Λ`-module coefficients; there is no
  construction of `ℱ_ρ` in this library.  So the sheaf is a variable `F` of
  `Stacks.EtaleCohomology.EtaleModules`, and its being `ℱ_ρ` is carried by the pairing
  hypothesis, which only holds for that sheaf.  No functor standing in for the dictionary is
  introduced.
* **Tag 03ST in degree two, and Tag 03Q9.** The Galois action on `H²_c(X_{k̄}, ℱ_ρ)`.
  `Stacks.Frobenius.fibreComparison_galoisStalkAction` carries Tag 03ST in degree zero only, and
  there is no Galois action on `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup`
  anywhere in the library.  So that action is the hypothesis `galois`.
* **Tags 03VJ, 0BTX and 0BNE.** The fundamental exact sequence
  `1 → π₁(X_{k̄}, η̄) → π₁(X, η̄) → Gal(k^{sep}/k) → 1`.  The arithmetic fundamental group is the
  genuine `AlgebraicGeometry.EtaleFundamentalGroup`; the geometric one enters as a normal
  subgroup `N` together with an isomorphism of `π₁(X, η̄) ⧸ N` with the Galois group.
* **The trace isomorphism `H²_c(X_{k̄}, μ_n) = ℤ/nℤ`**, quoted inside the source's own proof and
  not separately tagged there.  It is carried by the nondegeneracy of the pairing.  Tag 0F7I,
  the independence of `H²_c` of the chosen compactification, is also absent, so the
  compactification remains an explicit argument as in Tag 0GJZ.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
* [Stacks Project, Tag 03UD](https://stacks.math.columbia.edu/tag/03UD), the coinvariants.
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ), `H^i_c`.
* [Stacks Project, Tag 03ST](https://stacks.math.columbia.edu/tag/03ST), the Galois action.
* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE), the exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v r w

namespace Stacks.EtaleCohomology

/-- Successive application of a representation is application at the product. -/
private lemma representation_mul_apply {Λ : Type r} [Ring Λ] {M : Type w} [AddCommGroup M]
    [Module Λ M] {G : Type*} [Monoid G] (ρ : Representation Λ G M) (a b : G) (x : M) :
    ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

/-! ### Multiplication by a central scalar -/

section CentralScalar

variable (n : ℕ) (Λ : Type r) [Ring Λ] [Algebra (ZMod n) Λ]
  (M : Type w) [AddCommGroup M] [Module Λ M]

/-- Multiplication by an element of `ZMod n`, through the structural map `ZMod n → Λ`, as a
`Λ`-linear endomorphism of a `Λ`-module.  It is `Λ`-linear because the image of the structural
map of an algebra is central, which is what lets the Tate twist below be a twist by `Λ`-linear
maps even for a noncommutative `Λ`. -/
public def centralScalar (c : ZMod n) : M →ₗ[Λ] M where
  toFun m := algebraMap (ZMod n) Λ c • m
  map_add' _ _ := smul_add _ _ _
  map_smul' l m := by
    change algebraMap (ZMod n) Λ c • (l • m) = l • (algebraMap (ZMod n) Λ c • m)
    rw [smul_smul, smul_smul, Algebra.commutes]

/-- `centralScalar c` is scalar multiplication by the image of `c` in `Λ`. -/
@[simp]
public lemma centralScalar_apply (c : ZMod n) (m : M) :
    centralScalar n Λ M c m = algebraMap (ZMod n) Λ c • m := rfl

/-- Multiplying by `c` and then by `d` is multiplying by `c * d`. -/
public lemma centralScalar_centralScalar (c d : ZMod n) (m : M) :
    centralScalar n Λ M c (centralScalar n Λ M d m) = centralScalar n Λ M (c * d) m := by
  simp only [centralScalar_apply, smul_smul, ← map_mul]

/-- Multiplication by `1` is the identity. -/
@[simp]
public lemma centralScalar_one (m : M) : centralScalar n Λ M 1 m = m := by
  simp

/-- Multiplication by a unit of `ZMod n` is undone by multiplication by its inverse. -/
public lemma centralScalar_units_inv_centralScalar (c : (ZMod n)ˣ) (m : M) :
    centralScalar n Λ M ((c⁻¹ : (ZMod n)ˣ) : ZMod n)
        (centralScalar n Λ M (c : ZMod n) m) = m := by
  rw [centralScalar_centralScalar, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    centralScalar_one]

end CentralScalar

/-! ### The cyclotomic character -/

section Cyclotomic

variable (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep] (n : ℕ)

/-- The absolute Galois group acting by ring automorphisms.  This is the form in which Mathlib's
cyclotomic character takes its argument. -/
public def galoisRingEquivHom : (ksep ≃ₐ[k] ksep) →* (ksep ≃+* ksep) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The action of the Galois group on the `n`-th roots of unity of a separable closure. -/
public def galoisRootsOfUnity (σ : ksep ≃ₐ[k] ksep) :
    rootsOfUnity n ksep →* rootsOfUnity n ksep :=
  restrictRootsOfUnity σ n

/-- `galoisRootsOfUnity σ` applies `σ` to a root of unity. -/
@[simp]
public lemma galoisRootsOfUnity_coe (σ : ksep ≃ₐ[k] ksep) (ζ : rootsOfUnity n ksep) :
    ((galoisRootsOfUnity k ksep n σ ζ : ksepˣ) : ksep) = σ ((ζ : ksepˣ) : ksep) := rfl

variable [IsSepClosed ksep] [NeZero n] [NeZero (n : ksep)]

/-- **The mod-`n` cyclotomic character of `Gal(k^{sep}/k)`.**  A separably closed field in which
`n` is invertible has exactly `n` roots of unity of order dividing `n`, so Mathlib's
`modularCyclotomicCharacter` applies; `σ` raises every such root of unity to the power
`χ_cycl(σ)`.  This is the reduction mod `n` of the character `χ_cycl` of the source. -/
@[sga "7 IX 4.2" "partial"]
public def cyclotomicCharacterModN : (ksep ≃ₐ[k] ksep) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter ksep
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity ksep n)).comp (galoisRingEquivHom k ksep)

/-- **The cyclotomic character computes the Galois action on roots of unity.**  Inside the group
of `n`-th roots of unity of a separable closure, `σ` is the `χ_cycl(σ)`-th power map. -/
@[sga "7 IX 4.2" "finite-level description"]
public lemma galoisRootsOfUnity_eq_pow (σ : ksep ≃ₐ[k] ksep) (ζ : rootsOfUnity n ksep) :
    galoisRootsOfUnity k ksep n σ ζ =
      ζ ^ ((cyclotomicCharacterModN k ksep n σ : ZMod n)).val := by
  have hspec : galoisRingEquivHom k ksep σ ((ζ : ksepˣ) : ksep) =
      ((ζ : ksepˣ) : ksep) ^ ((cyclotomicCharacterModN k ksep n σ : ZMod n)).val :=
    modularCyclotomicCharacter.spec ksep _ _ ζ.2
  refine rootsOfUnity.coe_injective ?_
  change ((galoisRootsOfUnity k ksep n σ ζ : ksepˣ) : ksep) =
    (((ζ ^ ((cyclotomicCharacterModN k ksep n σ : ZMod n)).val : rootsOfUnity n ksep) :
      ksepˣ) : ksep)
  rw [galoisRootsOfUnity_coe]
  push_cast
  exact hspec

end Cyclotomic

/-! ### The residual action on the coinvariants of a normal subgroup -/

section Coinvariants

variable {Λ : Type r} [Ring Λ] {M : Type w} [AddCommGroup M] [Module Λ M]
  {G : Type*} [Group G] (ρ : Representation Λ G M) (N : Subgroup G) [N.Normal]

/-- The differences `g m - m` for `g` in a normal subgroup are carried into themselves by the
action of the ambient group: conjugating `g` stays inside the subgroup. -/
public lemma coinvariantsKer_le_comap (g : G) :
    Stacks.Trace.coinvariantsKer (ρ.comp N.subtype) ≤
      (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)).comap (ρ g) := by
  rw [Stacks.Trace.coinvariantsKer, Submodule.span_le]
  rintro _ ⟨⟨s, m⟩, rfl⟩
  have hs : g * (s : G) * g⁻¹ ∈ N := ‹N.Normal›.conj_mem (s : G) s.2 g
  have hkey : ρ g (ρ (s : G) m - m) =
      ρ ((⟨g * (s : G) * g⁻¹, hs⟩ : N) : G) (ρ g m) - ρ g m := by
    rw [map_sub]
    refine congrArg (· - ρ g m) ?_
    rw [← representation_mul_apply ρ, ← representation_mul_apply ρ, inv_mul_cancel_right]
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  change ρ g (ρ (s : G) m - m) ∈ Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)
  rw [hkey]
  exact Submodule.subset_span ⟨(⟨g * (s : G) * g⁻¹, hs⟩, ρ g m), rfl⟩

/-- The action of an element of the ambient group on the coinvariants of a normal subgroup. -/
public def normalCoinvariantsMap (g : G) :
    Stacks.Trace.coinvariants (ρ.comp N.subtype) →ₗ[Λ]
      Stacks.Trace.coinvariants (ρ.comp N.subtype) :=
  Submodule.mapQ _ _ (ρ g) (coinvariantsKer_le_comap ρ N g)

/-- `normalCoinvariantsMap g` sends the class of `m` to the class of `g m`. -/
@[simp]
public lemma normalCoinvariantsMap_mk (g : G) (m : M) :
    normalCoinvariantsMap ρ N g (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) =
      Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) (ρ g m) := rfl

/-- **The ambient group acts on the coinvariants of a normal subgroup.** -/
public def normalCoinvariantsRepresentation :
    Representation Λ G (Stacks.Trace.coinvariants (ρ.comp N.subtype)) where
  toFun := normalCoinvariantsMap ρ N
  map_one' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)).mkQ_surjective q
    change normalCoinvariantsMap ρ N 1
      (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) = _
    rw [normalCoinvariantsMap_mk, map_one]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)).mkQ_surjective q
    change normalCoinvariantsMap ρ N (a * b)
      (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) = _
    rw [normalCoinvariantsMap_mk, representation_mul_apply ρ]
    rfl

/-- The action of `g` on the coinvariants of `N` sends the class of `m` to the class of `g m`. -/
@[simp]
public lemma normalCoinvariantsRepresentation_apply_mk (g : G) (m : M) :
    normalCoinvariantsRepresentation ρ N g
        (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) =
      Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) (ρ g m) := rfl

/-- The normal subgroup itself acts trivially on its coinvariants, which is what makes the
action factor through the quotient group. -/
@[sga "4½ Rapport 5.10" "special case"]
public instance isTrivial_normalCoinvariantsRepresentation :
    Representation.IsTrivial ((normalCoinvariantsRepresentation ρ N).comp N.subtype) where
  out s := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)).mkQ_surjective q
    change normalCoinvariantsRepresentation ρ N (s : G)
      (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) = _
    rw [normalCoinvariantsRepresentation_apply_mk]
    exact Stacks.Trace.coinvariantsMk_group_action (ρ.comp N.subtype) s m

/-- **The quotient group acts on the coinvariants of a normal subgroup.** -/
@[sga "7 I 6.2"]
public def quotientCoinvariantsRepresentation :
    Representation Λ (G ⧸ N) (Stacks.Trace.coinvariants (ρ.comp N.subtype)) :=
  Representation.ofQuotient (normalCoinvariantsRepresentation ρ N) N

/-- The action of the class of `g` in `G ⧸ N` sends the class of `m` to the class of `g m`. -/
@[simp]
public lemma quotientCoinvariantsRepresentation_mk_mk (g : G) (m : M) :
    quotientCoinvariantsRepresentation ρ N (g : G ⧸ N)
        (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) =
      Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) (ρ g m) := rfl

variable {k : Type u} [Field k] {ksep : Type u} [Field ksep] [Algebra k ksep]

/-- **The Galois action on the geometric coinvariants.**  Along an identification of the quotient
`π₁(X, η̄) ⧸ π₁(X_{k̄}, η̄)` with `Gal(k^{sep}/k)` coming from the fundamental exact sequence, the
residual action of the quotient group becomes an action of the Galois group. -/
@[sga "7 I 6.2"]
public def galoisCoinvariantsRepresentation (φ : G ⧸ N ≃* (ksep ≃ₐ[k] ksep)) :
    Representation Λ (ksep ≃ₐ[k] ksep) (Stacks.Trace.coinvariants (ρ.comp N.subtype)) :=
  (quotientCoinvariantsRepresentation ρ N).comp φ.symm.toMonoidHom

/-- The Galois element `φ(g N)` acts on the coinvariants of `N` by sending the class of `m` to the
class of `g m`. -/
public lemma galoisCoinvariantsRepresentation_apply_mk (φ : G ⧸ N ≃* (ksep ≃ₐ[k] ksep))
    (g : G) (m : M) :
    galoisCoinvariantsRepresentation ρ N φ (φ (g : G ⧸ N))
        (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) =
      Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) (ρ g m) := by
  change quotientCoinvariantsRepresentation ρ N (φ.symm (φ (g : G ⧸ N))) _ = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Coinvariants

/-! ### The Tate twist by minus one -/

section TateTwist

variable (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep] [IsSepClosed ksep]
  (n : ℕ) [NeZero n] [NeZero (n : ksep)] (Λ : Type r) [Ring Λ] [Algebra (ZMod n) Λ]
  {M : Type w} [AddCommGroup M] [Module Λ M]

/-- **The Tate twist by `-1` of a `Gal(k^{sep}/k)`-module.**  The underlying `Λ`-module is
unchanged and `σ` acts by `χ_cycl(σ)⁻¹` composed with `σ`, which is the twist as the source
defines it.  The scalar `χ_cycl(σ)⁻¹` is central in `Λ`, so the twisted action is again by
`Λ`-linear maps, and it is an action because the character is multiplicative and `σ` acts
`Λ`-linearly. -/
public def tateTwistNegOne (τ : Representation Λ (ksep ≃ₐ[k] ksep) M) :
    Representation Λ (ksep ≃ₐ[k] ksep) M where
  toFun σ :=
    (centralScalar n Λ M (((cyclotomicCharacterModN k ksep n σ)⁻¹ : (ZMod n)ˣ) : ZMod n)).comp
      (τ σ)
  map_one' := by
    refine LinearMap.ext fun m => ?_
    change centralScalar n Λ M
      (((cyclotomicCharacterModN k ksep n 1)⁻¹ : (ZMod n)ˣ) : ZMod n) (τ 1 m) = m
    rw [map_one, map_one]
    simp
  map_mul' σ σ' := by
    refine LinearMap.ext fun m => ?_
    change algebraMap (ZMod n) Λ
        (((cyclotomicCharacterModN k ksep n (σ * σ'))⁻¹ : (ZMod n)ˣ) : ZMod n) •
        τ (σ * σ') m =
      algebraMap (ZMod n) Λ (((cyclotomicCharacterModN k ksep n σ)⁻¹ : (ZMod n)ˣ) : ZMod n) •
        τ σ (algebraMap (ZMod n) Λ
          (((cyclotomicCharacterModN k ksep n σ')⁻¹ : (ZMod n)ˣ) : ZMod n) • τ σ' m)
    rw [map_smul, smul_smul, ← map_mul, ← Units.val_mul, ← mul_inv,
      ← map_mul (cyclotomicCharacterModN k ksep n), representation_mul_apply τ]

/-- In the Tate twist `M(-1)`, `σ` acts by `χ_cycl(σ)⁻¹` times its action on `M`. -/
public lemma tateTwistNegOne_apply (τ : Representation Λ (ksep ≃ₐ[k] ksep) M)
    (σ : ksep ≃ₐ[k] ksep) (m : M) :
    tateTwistNegOne k ksep n Λ τ σ m =
      algebraMap (ZMod n) Λ (((cyclotomicCharacterModN k ksep n σ)⁻¹ : (ZMod n)ˣ) : ZMod n) •
        τ σ m := rfl

/-- **From a `χ_cycl`-twisted intertwining relation to equivariance for the Tate twist.**  A
`Λ`-linear map which turns the action of `σ` on its source into `χ_cycl(σ)⁻¹` times the action
of `σ` on its target is exactly a map of `Gal(k^{sep}/k)`-modules into the Tate twist by `-1`.
This is the bookkeeping that puts the `(-1)` of the source into the statement. -/
public lemma eq_tateTwistNegOne_of_centralScalar_eq {A : Type v} [AddCommGroup A]
    [Module Λ A]
    (τ : Representation Λ (ksep ≃ₐ[k] ksep) M) (α : Representation Λ (ksep ≃ₐ[k] ksep) A)
    (θ : A →ₗ[Λ] M) (σ : ksep ≃ₐ[k] ksep) (x : A)
    (h : centralScalar n Λ M (cyclotomicCharacterModN k ksep n σ : ZMod n) (θ (α σ x)) =
      τ σ (θ x)) :
    θ (α σ x) = tateTwistNegOne k ksep n Λ τ σ (θ x) := by
  have hdiv := congrArg (centralScalar n Λ M
    (((cyclotomicCharacterModN k ksep n σ)⁻¹ : (ZMod n)ˣ) : ZMod n)) h
  rwa [centralScalar_units_inv_centralScalar] at hdiv

end TateTwist

/-! ### Tag 03VK as an isomorphism of Galois modules -/

section CompactSupportTwo

attribute [local instance] HasDerivedCategory.standard

variable (ksep : Type u) [Field ksep] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of ksep))
  [LocallyOfFiniteType fbar] [QuasiCompact fbar] [IsSeparated fbar]
  (jbar : CompactificationOf (Over.mk fbar))
  (Λ : Type r) [Ring Λ] (F : EtaleModules.{u, r} Λ Xbar)

/-- The degree-two compactly supported cohomology module of a sheaf of `Λ`-modules on the
geometric curve: the module `H²_c` of Tag 0GJZ, taken at the sheaf placed in degree zero. -/
public abbrev compactlySupportedCohomologyTwo : ModuleCat.{max (u + 1) r} Λ :=
  (compactlySupportedCohomologyGroup.{u, r} ksep fbar jbar Λ 2).obj
    ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ Xbar) 0).obj F)

end CompactSupportTwo

section Tag03VK

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep] [IsSepClosed ksep]
  {X Xbar : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [ConnectedSpace X]
  (fbar : Xbar ⟶ Spec (.of ksep)) (jbar : CompactificationOf (Over.mk fbar))
  (Λ : Type r) [Ring Λ] (F : EtaleModules.{u, r} Λ Xbar)
  (n : ℕ) [NeZero n] [NeZero (n : ksep)] [Algebra (ZMod n) Λ]
  {M : Type w} [AddCommGroup M] [Module Λ M]

/-- **Stacks Project, Tag 03VK, as an isomorphism of `Gal(k^{sep}/k)`-modules.**

The right-hand side is built here: `Stacks.Trace.coinvariants` of the restriction of `ρ` to the
geometric fundamental group `N`, carrying the residual Galois action of
`Stacks.EtaleCohomology.galoisCoinvariantsRepresentation` through the fundamental exact sequence
`φ`, Tate-twisted by `-1` as the source defines the twist.  The left-hand side is the compactly
supported cohomology module of Tag 0GJZ in degree two, carrying the Galois action `galois`.

The geometric input is a pairing of `H²_c` with the `n`-th roots of unity, taking values in the
coinvariants, equivariant for the Galois actions on all three of its arguments and nondegenerate
at one root of unity `ζ₀`.  That is the shape in which the source supplies it: the twist in the
conclusion is not assumed anywhere, it comes out of the computation of the Galois action on
`μ_n`, which is the cyclotomic character.  See the module docstring for the inputs carried as
hypotheses and the tags they belong to.

`hbase` pins `Xbar` as the geometric curve `X_{k̄} = X ×_k k^{sep}`, so that the cohomology on
the left is that of the base change and not of an unrelated scheme over `k^{sep}`; both the
projection `gbar` and the structure morphism `fbar` are determined by that one isomorphism, so
neither is an unconstrained choice.  The identification itself plays no part in the twist
bookkeeping, which is why the proof only destructures it. -/
@[stacks 03VK "the Galois-module conclusion, obtained from an equivariant nondegenerate pairing \
with μ_n coefficients. The right-hand side (M)_{π₁(X_k̄,η̄)}(-1) is constructed: coinvariants of \
Tag 03UD for the geometric fundamental group, the residual Gal(k^sep/k)-action through the \
fundamental exact sequence, and the Tate twist by -1 as the source defines it, χ_cycl(σ)⁻¹ \
composed with σ; the left-hand side is H²_c of Tag 0GJZ. Four inputs are explicit hypotheses \
because this library has no statement for them: the sheaf ℱ_ρ attached to ρ, which is Tag 0DV5 \
part (1), that is Tag 03RV and hence Tag 0245, so the sheaf is a variable and its link to ρ is \
carried by the pairing; the Galois action on H²_c and its compatibility, Tag 03ST in degree two, \
of which only degree zero is available here, through Tag 03Q9; the fundamental exact sequence, Tags \
03VJ, 0BTX and 0BNE, carried by the normal subgroup N and the isomorphism φ; and the trace \
isomorphism H²_c(X_k̄, μ_n) = ℤ/nℤ quoted inside the source's proof, carried by the \
nondegeneracy of the pairing. Tag 0F7I being absent, the compactification is an explicit \
argument as in Tag 0GJZ, and Xbar is pinned as the base change X ×_k k^sep by hbase. What is \
proved is that these inputs produce the twisted equivariant isomorphism: the Tate twist and the \
Galois equivariance of the identification"]
public theorem compactlySupportedCohomologyTwo_galoisIso_tateTwistCoinvariants
    [LocallyOfFiniteType fbar] [QuasiCompact fbar] [IsSeparated fbar]
    [IsCurve k fX] [Smooth fX] [GeometricallyConnected fX]
    (gbar : Xbar ⟶ X)
    (hbase : ∃ e : Xbar ≅ pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k ksep))),
      gbar = e.hom ≫ pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) ∧
        fbar = e.hom ≫ pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k ksep))))
    (etabar : AlgebraicGeometry.GeometricPoint X)
    (ρ : Representation Λ (EtaleFundamentalGroup X etabar) M)
    (N : Subgroup (EtaleFundamentalGroup X etabar)) [N.Normal]
    (φ : EtaleFundamentalGroup X etabar ⧸ N ≃* (ksep ≃ₐ[k] ksep))
    (galois : Representation Λ (ksep ≃ₐ[k] ksep)
      (compactlySupportedCohomologyTwo.{u, r} ksep fbar jbar Λ F))
    (pair : Additive (rootsOfUnity n ksep) →+
      (compactlySupportedCohomologyTwo.{u, r} ksep fbar jbar Λ F →ₗ[Λ]
        Stacks.Trace.coinvariants (ρ.comp N.subtype)))
    (hpair : ∀ (σ : ksep ≃ₐ[k] ksep) (ζ : rootsOfUnity n ksep)
        (x : compactlySupportedCohomologyTwo.{u, r} ksep fbar jbar Λ F),
      pair (Additive.ofMul (galoisRootsOfUnity k ksep n σ ζ)) (galois σ x) =
        galoisCoinvariantsRepresentation ρ N φ σ (pair (Additive.ofMul ζ) x))
    (ζ₀ : rootsOfUnity n ksep)
    (hζ₀ : Function.Bijective (pair (Additive.ofMul ζ₀))) :
    ∃ θ : compactlySupportedCohomologyTwo.{u, r} ksep fbar jbar Λ F ≃ₗ[Λ]
        Stacks.Trace.coinvariants (ρ.comp N.subtype),
      ∀ (σ : ksep ≃ₐ[k] ksep)
        (x : compactlySupportedCohomologyTwo.{u, r} ksep fbar jbar Λ F),
        θ (galois σ x) =
          tateTwistNegOne k ksep n Λ (galoisCoinvariantsRepresentation ρ N φ) σ (θ x) := by
  -- The identification of `Xbar` with the base change is in the statement, not in the argument.
  obtain ⟨-, -, -⟩ := hbase
  refine ⟨LinearEquiv.ofBijective (pair (Additive.ofMul ζ₀)) hζ₀, fun σ x => ?_⟩
  change pair (Additive.ofMul ζ₀) (galois σ x) =
    tateTwistNegOne k ksep n Λ (galoisCoinvariantsRepresentation ρ N φ) σ
      (pair (Additive.ofMul ζ₀) x)
  refine eq_tateTwistNegOne_of_centralScalar_eq k ksep n Λ
    (galoisCoinvariantsRepresentation ρ N φ) galois (pair (Additive.ofMul ζ₀)) σ x ?_
  -- The pairing turns the Galois translate of `ζ₀` into `χ_cycl(σ)` times the pairing at `ζ₀`.
  have hpow : pair (Additive.ofMul (galoisRootsOfUnity k ksep n σ ζ₀)) =
      ((cyclotomicCharacterModN k ksep n σ : ZMod n)).val • pair (Additive.ofMul ζ₀) := by
    rw [galoisRootsOfUnity_eq_pow, ofMul_pow, map_nsmul]
  have hstep := hpair σ ζ₀ x
  rw [hpow, LinearMap.smul_apply] at hstep
  -- That natural-number multiple is multiplication by the central scalar `χ_cycl(σ)`.
  have hcast : ((((cyclotomicCharacterModN k ksep n σ : ZMod n)).val : ℕ) : Λ) =
      algebraMap (ZMod n) Λ (cyclotomicCharacterModN k ksep n σ : ZMod n) := by
    rw [← map_natCast (algebraMap (ZMod n) Λ)]
    congr 1
    simp
  rwa [centralScalar_apply, ← hcast, Nat.cast_smul_eq_nsmul]

end Tag03VK

end Stacks.EtaleCohomology

end
