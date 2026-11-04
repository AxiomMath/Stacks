module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResidues
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorComaximal
public import StacksFrontier.RingTheory.Derivation.ConductorBranch
public import StacksFrontier.RingTheory.Nagata.Japanese
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two branch residues of a node on the global normalization: item (3) of Stacks 0E68

Let `k` be a separably closed field, let `A` be a reduced Nagata `k`-algebra of dimension at most
one whose singularities are a finite family of distinct maximal ideals `𝔪₁, …, 𝔪ᵤ`, each a node,
and let `A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions. Item (1) of Stacks 0E68
(`Stacks.Curves.exists_adjoin_eq_integralClosure_of_isNodalAlgebra`) produces a single `t` with
`A [t] = A'` and `t ^ 2 = a + c t`, and item (2)
(`Stacks.Curves.exists_mem_prod_mul_add_mul_eq_one_of_isNodalAlgebra`) an element of the
conductor comaximal with `2 t - c`. Item (3) is the remaining datum: at each node `𝔪ᵢ`, two
`k`-algebra maps `ε₁, ε₂ : A' → k` which agree on `A`, are normalized by `ε₁ t - ε₂ t = 1`, and
cut out `𝔪ᵢ` on `A` — the residues at the two points of the normalization above the node.

The three steps are transport, normalization and the conductor.

**Transport.** `Stacks.Curves.exists_branchResidues_of_quadraticAlgebra_algEquiv_prod` produces
the two residues at a *local* ring, from the splitting of its quadratic algebra, and gives only
`ε₁ ≠ ε₂`. That inequality becomes the separation of the generator, `ε₁ t ≠ ε₂ t`, because
`A' = A + A t`: two residues agreeing on `A` and at `t` agree everywhere
(`Stacks.Curves.apply_ne_apply_of_sup_span_eq_top`). The local statement is then carried to the
global `A'` along the map `A' → A'_{𝔪ᵢ}` followed by
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`, the pattern of
`Stacks.Curves.four_mul_add_mul_self_notMem_of_isNodalAlgebra`.

**Normalization.** The local statement gives `ε₁ t ≠ ε₂ t`, not `ε₁ t - ε₂ t = 1`. Rescaling `t`
by the unit `(ε₁ t - ε₂ t)⁻¹` of `k` preserves `A + A t = A'` and the quadratic shape, with `a`
and `c` rescaled, and normalizes the difference
(`Stacks.Curves.exists_sup_span_eq_top_and_apply_sub_eq_one`). The rescaling is by a scalar of
`k` and therefore depends on the node: a single generator cannot be normalized at two nodes at
once, which is why the conclusion below quantifies over the nodes outside the generator.

**The conductor.** The kernel of `ε₁ ∘ algebraMap A A'` is exactly `𝔪ᵢ`, because a `k`-algebra
map to `k` is surjective and its kernel is therefore maximal, hence the maximal ideal after
localizing at `𝔪ᵢ`. What the extension theorem then needs is that this kernel lie inside the
conductor, and *that is false as soon as there are two nodes*: the conductor of `A` in `A'` is
the product `𝔪₁ ⋯ 𝔪ᵤ`, and `𝔪ᵢ ⊆ 𝔪₁ ⋯ 𝔪ᵤ` fails for `u ≥ 2`. For two disjoint nodal cubics,
`A = A₁ × A₂` with `A₁ = A₂ = {h ∈ k[s] : h 1 = h (-1)}` and `A' = k[s] × k[s]`, the element
`(0, 1)` of `𝔪₁ = m × A₂` carries `(0, s) ∈ A'` to `(0, s) ∉ A`. What is true is the containment
after multiplying by one element invertible at the node, `α₀ · 𝔪ᵢ ⊆ 𝔪₁ ⋯ 𝔪ᵤ` for `α₀` in
`∏_{j ≠ i} 𝔪ⱼ` outside `𝔪ᵢ`, and that is the hypothesis of
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor_mul`.

## Main results

* `Stacks.Curves.apply_ne_apply_of_sup_span_eq_top` — two residues agreeing on `A` and at a
  module generator of `A'` over `A` are equal.
* `Stacks.Curves.apply_algebraMap_eq_zero_iff_mem_maximalIdeal` — a `k`-algebra map to `k` cuts
  out the maximal ideal of a local ring.
* `Stacks.Curves.exists_branchResidues_apply_ne_of_quadraticAlgebra_algEquiv_prod` — the two
  branch residues at a split local node, separated by a generator.
* `Stacks.Curves.exists_branchResidues_of_isNodalAlgebra` — **item (3) before normalization**:
  on the global `A'`, two residues agreeing on `A`, separated by the generator, and cutting out
  the node.
* `Stacks.Curves.exists_sup_span_eq_top_and_apply_sub_eq_one` — the rescaling of a generator that
  normalizes the difference of two residues to `1`.
* `Stacks.Curves.existsUnique_extend_integralClosure_branchResidues_of_isNodalAlgebra` — **items
  (1), (2) and (3) together**: at each node a generator of `A'` over `A`, its quadratic relation,
  the two branch residues normalized and cutting out that node, and the unique extension of any
  `k`-derivation of `A` to `A'` fixing both points above the node.
* `Stacks.Curves.nonempty_residueField_localization_algEquiv_of_isAlgClosed` — over an
  algebraically closed field the residue field at a maximal ideal of a finite-type algebra is the
  base field, Zariski's lemma at a localization.
* `Stacks.Curves.existsUnique_extend_integralClosure_branchResidues_of_finiteType` — the same
  three items for a finite-type algebra over an algebraically closed field, where the rationality
  of the residue fields is no longer a hypothesis.

## Implementation notes

The splitting of the quadratic algebra is taken at an abstract local ring and transported, never
at `Localization.AtPrime 𝔪` directly: the instance
`Module (ResidueField R) (quadraticAlgebra R)` is not found within the `synthInstance` budget
when `R` is a localization, which is the reason
`Stacks.Curves.four_mul_add_mul_self_notMem_of_isNodalAlgebra` is split the same way. The
rationality of the residue field at the node is a hypothesis of the first form of the result and
discharged in the second: over an algebraically closed field it is Zariski's lemma, which for a
finite-type algebra is
`Stacks.Curves.nonempty_residueField_localization_algEquiv_of_isAlgClosed` and at a stalk is
`Stacks.Curves.nonempty_residueField_stalk_algEquiv_of_isClosed`.

No `@[stacks]` tag is carried here. Item (3) is one of the three items of Stacks 0E68, and the
last statement, while it does state all three, states them for an affine `k`-algebra presented by
its node locus rather than for a proper connected at-worst-nodal curve, and it proves only the
right-to-left direction of the tag's equality of sets of vector fields.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w

namespace Stacks.Curves

/-! ### Two residues agreeing on the base are determined by a generator -/

section Separate

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

/-- Alias of `Stacks.DerivationExtension.coe_algebraMap_integralClosure`. -/
private alias coe_algebraMap_integralClosure :=
  Stacks.DerivationExtension.coe_algebraMap_integralClosure

omit [IsLocalization (nonZeroDivisors A) L] in
/-- **Two distinct residues differ at a generator.** If the image of `A` in its integral closure
`A'` together with a single `τ` spans `A'` as an `A`-module, then two `k`-algebra maps
`A' → k` agreeing on `A` and at `τ` are equal; so two distinct such maps differ at `τ`.

This is what upgrades the inequality `ε₁ ≠ ε₂` of
`Stacks.Curves.exists_branchResidues_of_quadraticAlgebra_algEquiv_prod` to the inequality
`ε₁ τ ≠ ε₂ τ` that the normalization of the generator needs. -/
public theorem apply_ne_apply_of_sup_span_eq_top (τ : ↥(integralClosure A L))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {τ} = ⊤)
    (ε₁ ε₂ : ↥(integralClosure A L) →ₐ[k] k)
    (hres : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) =
      ε₂ (algebraMap A ↥(integralClosure A L) b))
    (hne : ε₁ ≠ ε₂) : ε₁ τ ≠ ε₂ τ := by
  intro hτ
  refine hne (AlgHom.ext fun z => ?_)
  obtain ⟨a₀, a₁, hz⟩ :=
    Stacks.DerivationExtension.exists_add_mul_of_sup_span_eq_top τ hspan z.2
  have hzT : z = algebraMap A ↥(integralClosure A L) a₀ +
      algebraMap A ↥(integralClosure A L) a₁ * τ :=
    Subtype.ext (by
      simpa only [Subalgebra.coe_add, Subalgebra.coe_mul,
        coe_algebraMap_integralClosure] using hz)
  rw [hzT, map_add, map_add, map_mul, map_mul, hres a₀, hres a₁, hτ]

end Separate

/-! ### A residue cuts out the maximal ideal of a local ring -/

/-- **A `k`-algebra map to `k` cuts out the maximal ideal.** Let `R` be a local `k`-algebra, let
`B` be an `R`-algebra and let `ε : B →ₐ[k] k`. Then `b : R` is killed by `ε` exactly when it lies
in the maximal ideal of `R`.

The composite `R → B → k` is a `k`-algebra map to `k`, hence surjective, so its kernel is a
maximal ideal of `R` and therefore *the* maximal ideal. This is how the branch residues of a node
are identified as cutting out the node. -/
public theorem apply_algebraMap_eq_zero_iff_mem_maximalIdeal (k : Type u) (R : Type v)
    (B : Type w) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R] [CommRing B]
    [Algebra R B] [Algebra k B] [IsScalarTower k R B] (ε : B →ₐ[k] k) (r : R) :
    ε (algebraMap R B r) = 0 ↔ r ∈ maximalIdeal R := by
  let φ : R →ₐ[k] k := ε.comp (IsScalarTower.toAlgHom k R B)
  rw [← IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective φ fun c => ⟨algebraMap k R c, φ.commutes c⟩)]
  exact RingHom.mem_ker.symm

/-! ### The two branch residues at a split local node -/

/-- **The two branch residues of a split node, separated by a generator.** Let `R` be a local
`k`-algebra whose residue field is `k` and whose quadratic algebra is the split one `κ × κ`, and
let the image of `R` in its normalization `R'` together with a single `τ` span `R'`. Then `R'`
carries two `k`-algebra maps to `k` which agree on `R` and differ at `τ`.

This is `Stacks.Curves.exists_branchResidues_of_quadraticAlgebra_algEquiv_prod` with its
conclusion `ε₁ ≠ ε₂` sharpened by
`Stacks.Curves.apply_ne_apply_of_sup_span_eq_top`. -/
public theorem exists_branchResidues_apply_ne_of_quadraticAlgebra_algEquiv_prod (k : Type u)
    (R : Type v) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (eκ : ResidueField R ≃ₐ[k] k)
    (e : quadraticAlgebra R ≃ₐ[ResidueField R] (ResidueField R × ResidueField R))
    (τ : ↥(integralClosure R (FractionRing R)))
    (hspan : LinearMap.range (Algebra.linearMap R ↥(integralClosure R (FractionRing R))) ⊔
      Submodule.span R {τ} = ⊤) :
    ∃ ε₁ ε₂ : ↥(integralClosure R (FractionRing R)) →ₐ[k] k,
      (∀ r : R, ε₁ (algebraMap R ↥(integralClosure R (FractionRing R)) r) =
          ε₂ (algebraMap R ↥(integralClosure R (FractionRing R)) r)) ∧
        ε₁ τ ≠ ε₂ τ := by
  obtain ⟨ε₁, ε₂, hres, hne⟩ :=
    exists_branchResidues_of_quadraticAlgebra_algEquiv_prod k R eκ e
  exact ⟨ε₁, ε₂, hres, apply_ne_apply_of_sup_span_eq_top τ hspan ε₁ ε₂ hres hne⟩

/-! ### Item (3) on the global normalization -/

/-- An isomorphism of algebras carries the image of the base onto the image of the base. -/
private theorem map_range_algebra_linearMap {R B C : Type*} [CommRing R] [CommRing B]
    [CommRing C] [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) :
    Submodule.map (e.toLinearEquiv : B →ₗ[R] C) (LinearMap.range (Algebra.linearMap R B)) =
      LinearMap.range (Algebra.linearMap R C) := by
  rw [← LinearMap.range_comp]
  exact congrArg LinearMap.range (LinearMap.ext fun r => e.commutes r)

/-- **Item (3) of Stacks 0E68, before normalization.** Let `k` be separably closed, let `A` be a
reduced Nagata `k`-algebra, let `A'` be its normalization inside its total ring of fractions, and
let `𝔪` be a prime of `A` at which the local ring is a nodal `k`-algebra with residue field `k`.
Let the image of `A` together with a single `t` span `A'`. Then `A'` carries two `k`-algebra maps
to `k` which agree on `A`, differ at `t`, and cut out `𝔪` on `A`.

These are the residues at the two points of the normalization above the node. The statement is
`Stacks.Curves.exists_branchResidues_apply_ne_of_quadraticAlgebra_algEquiv_prod`, which is about
a local ring, transported to the global `A'` along
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`; the kernel is
identified by `Stacks.Curves.apply_algebraMap_eq_zero_iff_mem_maximalIdeal`. The difference
`ε₁ t - ε₂ t` is a nonzero scalar, not `1`; normalizing it is
`Stacks.Curves.exists_sup_span_eq_top_and_apply_sub_eq_one`. -/
public theorem exists_branchResidues_of_isNodalAlgebra (k : Type u) (A : Type v) [Field k]
    [IsSepClosed k] [CommRing A] [IsReduced A] [Algebra k A] (hNagata : IsNagataRing A)
    (𝔪 : Ideal A) [𝔪.IsPrime] (hnodal : IsNodalAlgebra k (Localization.AtPrime 𝔪))
    (eκ : ResidueField (Localization.AtPrime 𝔪) ≃ₐ[k] k)
    (t : ↥(integralClosure A (FractionRing A)))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t} = ⊤) :
    ∃ ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k,
      (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
          ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) b)) ∧
        ε₁ t - ε₂ t ≠ 0 ∧
          ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) = 0 ↔ b ∈ 𝔪 := by
  classical
  have := hNagata
  let T := ↥(integralClosure A (FractionRing A))
  let Rl := Localization.AtPrime 𝔪
  let Tl := Localization (Algebra.algebraMapSubmonoid T 𝔪.primeCompl)
  let Dl := ↥(integralClosure Rl (FractionRing Rl))
  have hNagl : IsNagataRing Rl := isNagata_of_isLocalization A 𝔪.primeCompl Rl hNagata
  have : IsNoetherianRing Rl := IsLocalization.isNoetherianRing 𝔪.primeCompl Rl inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_localization_integralClosure_fractionRing A
    (minimalPrimes.finite_of_isNoetherianRing A) Rl 𝔪.primeCompl
  let ψ : T →+* Dl := (e : Tl →+* Dl).comp (algebraMap T Tl)
  have hψ : ∀ b : A, ψ (algebraMap A T b) = algebraMap Rl Dl (algebraMap A Rl b) := fun b => by
    show e (algebraMap T Tl (algebraMap A T b)) = algebraMap Rl Dl (algebraMap A Rl b)
    rw [← IsScalarTower.algebraMap_apply A T Tl, IsScalarTower.algebraMap_apply A Rl Tl,
      e.commutes]
  have hψk : ∀ c : k, ψ (algebraMap k T c) = algebraMap k Dl c := by
    intro c
    have h := hψ (algebraMap k A c)
    rwa [← IsScalarTower.algebraMap_apply k A T, ← IsScalarTower.algebraMap_apply k A Rl,
      ← IsScalarTower.algebraMap_apply k Rl Dl] at h
  have hspanTl : LinearMap.range (Algebra.linearMap Rl Tl) ⊔
      Submodule.span Rl {algebraMap T Tl t} = ⊤ := by
    have h := congrArg
      (fun N : Submodule A T => N.localized' Rl 𝔪.primeCompl
        (IsScalarTower.toAlgHom A T Tl).toLinearMap) hspan
    rwa [Submodule.localized'_sup, Submodule.localized'_range_algebraLinearMap,
      Submodule.localized'_span, Set.image_singleton, Submodule.localized'_top] at h
  have hspanD : LinearMap.range (Algebra.linearMap Rl Dl) ⊔ Submodule.span Rl {ψ t} = ⊤ := by
    have h := congrArg (Submodule.map (e.toLinearEquiv : Tl →ₗ[Rl] Dl)) hspanTl
    rwa [Submodule.map_sup, map_range_algebra_linearMap e, Submodule.map_span,
      Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h
  let : IsSepClosed (ResidueField Rl) := IsSepClosed.of_ringEquiv eκ.toRingEquiv
  obtain ⟨esplit⟩ := nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed k Rl hNagl hnodal
  obtain ⟨ε₁, ε₂, hres, hne⟩ :=
    exists_branchResidues_apply_ne_of_quadraticAlgebra_algEquiv_prod k Rl eκ esplit (ψ t) hspanD
  let ψk : T →ₐ[k] Dl := { ψ with commutes' := hψk }
  refine ⟨ε₁.comp ψk, ε₂.comp ψk, fun b => ?_, sub_ne_zero_of_ne hne, fun b => ?_⟩
  · show ε₁ (ψ (algebraMap A T b)) = ε₂ (ψ (algebraMap A T b))
    rw [hψ b]
    exact hres (algebraMap A Rl b)
  · show ε₁ (ψ (algebraMap A T b)) = 0 ↔ b ∈ 𝔪
    rw [hψ b, apply_algebraMap_eq_zero_iff_mem_maximalIdeal k Rl Dl ε₁ (algebraMap A Rl b)]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff Rl 𝔪 b

/-! ### Normalizing the generator against the two residues -/

/-- **Normalizing the generator so that the two residues differ by one.** Let the image of `A`
together with `t₀` span the normalization `A'`, with `t₀ ^ 2 = a₀ + c₀ t₀`, and let
`ε₁, ε₂ : A' →ₐ[k] k` satisfy `ε₁ t₀ ≠ ε₂ t₀`. Then rescaling `t₀` by the unit
`(ε₁ t₀ - ε₂ t₀)⁻¹` of `k` gives a generator `t` of `A'` over `A`, again with a monic quadratic
relation over `A`, for which `ε₁ t - ε₂ t = 1`.

This is the normalization that the extension theorem's hypothesis `ε₁ t - ε₂ t = 1` asks for and
that the local production of the branch residues does not give. It rescales by a scalar of `k`,
so it can be arranged at one node at a time. -/
public theorem exists_sup_span_eq_top_and_apply_sub_eq_one {k : Type u} {A : Type v} [Field k]
    [CommRing A] [Algebra k A] (t₀ : ↥(integralClosure A (FractionRing A))) (a₀ c₀ : A)
    (hspan₀ : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t₀} = ⊤)
    (hrel₀ : t₀ * t₀ = algebraMap A ↥(integralClosure A (FractionRing A)) a₀ +
      algebraMap A ↥(integralClosure A (FractionRing A)) c₀ * t₀)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k) (hne : ε₁ t₀ - ε₂ t₀ ≠ 0) :
    ∃ (t : ↥(integralClosure A (FractionRing A))) (a c : A),
      (LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
          Submodule.span A {t} = ⊤) ∧
        t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
            algebraMap A ↥(integralClosure A (FractionRing A)) c * t ∧
          ε₁ t - ε₂ t = 1 := by
  have hξ : IsUnit (algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hne)).map (algebraMap k A)
  refine ⟨algebraMap A ↥(integralClosure A (FractionRing A))
      (algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹) * t₀,
    algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹ * algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹ * a₀,
    algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹ * c₀, ?_, ?_, ?_⟩
  · rw [← Algebra.smul_def, Submodule.span_singleton_smul_eq hξ]
    exact hspan₀
  · simp only [map_mul]
    linear_combination (algebraMap A ↥(integralClosure A (FractionRing A))
      (algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹) * algebraMap A ↥(integralClosure A (FractionRing A))
        (algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹)) * hrel₀
  · have hε : ∀ ε : ↥(integralClosure A (FractionRing A)) →ₐ[k] k,
        ε (algebraMap A ↥(integralClosure A (FractionRing A))
          (algebraMap k A (ε₁ t₀ - ε₂ t₀)⁻¹)) = (ε₁ t₀ - ε₂ t₀)⁻¹ := by
      intro ε
      rw [← IsScalarTower.algebraMap_apply k A ↥(integralClosure A (FractionRing A))]
      exact ε.commutes _
    rw [map_mul, map_mul, hε ε₁, hε ε₂, ← mul_sub]
    exact inv_mul_cancel₀ hne

/-! ### Items (1), (2) and (3) together -/

/-- **Items (1), (2) and (3) of Stacks 0E68, and the extension at a node.** Let `k` be separably
closed, let `A` be a reduced Nagata `k`-algebra of dimension at most one whose singularities are
a finite family of distinct maximal ideals `𝔪ᵢ`, `i ∈ s`, each a node with residue field `k`,
and suppose every minimal prime of `A` is contained in one of them. Let `A'` be the normalization
of `A` inside its total ring of fractions. Then for each node `𝔪ᵢ` there are a single `t`
generating `A'` over `A` with `t ^ 2 = a + c t`, and two `k`-algebra maps `ε₁, ε₂ : A' → k` which

* agree on `A`,
* are normalized by `ε₁ t - ε₂ t = 1`,
* cut out `𝔪ᵢ` on `A`, and
* kill the unique extension to `A'` of any `k`-derivation of `A`,

so that the extension fixes both points of the normalization above `𝔪ᵢ`.

Item (1) is `Stacks.Curves.exists_adjoin_eq_integralClosure_of_isNodalAlgebra`, item (3) is
`Stacks.Curves.exists_branchResidues_of_isNodalAlgebra` followed by
`Stacks.Curves.exists_sup_span_eq_top_and_apply_sub_eq_one`, and item (2) is the pair
`Stacks.Curves.finite_setOf_isMaximal_two_mul_sub_mem`,
`Stacks.Curves.not_le_comap_of_isMaximal_two_mul_sub_mem` fed to
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor_mul`.

The generator depends on the node, since normalizing `ε₁ t - ε₂ t` to `1` rescales `t` by a
scalar of `k`; the extension `D'` does not, being the unique extension of `D`. The hypothesis on
the minimal primes is what makes the discriminant of the generator a nonzerodivisor, and it
cannot be dropped: for `A = k[x]`, already normal, item (1) is satisfied by `t = 0`, `a = c = 0`,
and `2 t - c = 0` lies in every maximal ideal of `A'`. -/
@[sga "7 X 2.33" "special case"]
public theorem existsUnique_extend_integralClosure_branchResidues_of_isNodalAlgebra (k : Type u)
    (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [IsReduced A] [Ring.KrullDimLE 1 A]
    [Algebra k A] (hNagata : IsNagataRing A) {ι : Type*} (𝔪 : ι → Ideal A) (s : Finset ι)
    (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔪 i ≠ 𝔪 j)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], (∀ i ∈ s, 𝔪 i ≠ P) →
      IsRegularLocalRing (Localization.AtPrime P))
    (hcomp : ∀ p ∈ minimalPrimes A, ∃ i ∈ s, p ≤ 𝔪 i)
    (eκ : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      Nonempty (ResidueField (Localization.AtPrime P) ≃ₐ[k] k)) :
    ∀ i ∈ s, ∃ (t : ↥(integralClosure A (FractionRing A))) (a c : A)
      (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k),
      Algebra.adjoin A ({(t : FractionRing A)} : Set (FractionRing A)) =
          integralClosure A (FractionRing A) ∧
        t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
            algebraMap A ↥(integralClosure A (FractionRing A)) c * t ∧
          (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
              ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) b)) ∧
            ε₁ t - ε₂ t = 1 ∧
              (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) = 0 ↔
                  b ∈ 𝔪 i) ∧
                ∀ D : Derivation k A A,
                  ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
                      ↥(integralClosure A (FractionRing A)),
                    (∀ b : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
                        algebraMap A ↥(integralClosure A (FractionRing A)) (D b)) ∧
                      (∀ z, ε₁ (D' z) = 0) ∧ (∀ z, ε₂ (D' z) = 0) := by
  classical
  have := hNagata
  intro i hi
  have := hmax i hi
  obtain ⟨eκi⟩ := eκ (𝔪 i) ⟨i, hi, rfl⟩
  obtain ⟨t₀, a₀, c₀, hS₀, hrel₀⟩ :=
    exists_adjoin_eq_integralClosure_of_isNodalAlgebra k A 𝔪 s hmax hdistinct hnodal hreg
  have hspan₀ :=
    Stacks.DerivationExtension.sup_span_eq_top_of_adjoin_eq_integralClosure t₀ a₀ c₀ hS₀ hrel₀
  obtain ⟨ε₁, ε₂, hres, hne₀, hker⟩ := exists_branchResidues_of_isNodalAlgebra k A hNagata
    (𝔪 i) (hnodal (𝔪 i) ⟨i, hi, rfl⟩) eκi t₀ hspan₀
  obtain ⟨t, a, c, hspan, hrel, hne⟩ :=
    exists_sup_span_eq_top_and_apply_sub_eq_one t₀ a₀ c₀ hspan₀ hrel₀ ε₁ ε₂ hne₀
  have hS := Stacks.DerivationExtension.adjoin_eq_integralClosure_of_sup_span_eq_top t hspan
  refine ⟨t, a, c, ε₁, ε₂, hS, hrel, hres, hne, hker, fun D => ?_⟩
  have hd : 4 * a + c * c ∈ nonZeroDivisors A := by
    refine Stacks.RingTheory.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes
      fun p hp hmem => ?_
    obtain ⟨j, hj, hple⟩ := hcomp p hp
    have := hmax j hj
    exact four_mul_add_mul_self_notMem_of_isNodalAlgebra k A (𝔪 j)
      (hnodal (𝔪 j) ⟨j, hj, rfl⟩) t a c hspan hrel (hple hmem)
  have hcond : ∀ α ∈ ∏ j ∈ s, 𝔪 j, ∃ β : A,
      algebraMap A ↥(integralClosure A (FractionRing A)) α * t =
        algebraMap A ↥(integralClosure A (FractionRing A)) β := by
    intro α hα
    obtain ⟨β, hβ⟩ := prod_smul_top_le_range_algebraMap_integralClosure_of_isNodalAlgebra k A 𝔪
      s hnodal hreg (Submodule.smul_mem_smul hα Submodule.mem_top)
    rw [Algebra.linearMap_apply] at hβ
    exact ⟨β, by rw [hβ, Algebra.smul_def]⟩
  have hnotle : ¬ (∏ j ∈ s.erase i, 𝔪 j) ≤ 𝔪 i := by
    intro hle
    obtain ⟨j, hj, hjle⟩ := (hmax i hi).isPrime.prod_le.mp hle
    exact hdistinct j (Finset.mem_of_mem_erase hj) i hi (Finset.ne_of_mem_erase hj)
      ((hmax j (Finset.mem_of_mem_erase hj)).eq_of_le (hmax i hi).ne_top hjle)
  obtain ⟨α₀, hα₀prod, hα₀notmem⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hcondε : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) = 0 →
      α₀ * b ∈ ∏ j ∈ s, 𝔪 j := by
    intro b hb
    rw [mul_comm, ← Finset.mul_prod_erase s 𝔪 hi]
    exact Ideal.mul_mem_mul ((hker b).mp hb) hα₀prod
  exact
    Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor_mul
      D t a c (∏ j ∈ s, 𝔪 j) hS hrel hcond
      (finite_setOf_isMaximal_two_mul_sub_mem A hNagata t a c hrel hd)
      (not_le_comap_of_isMaximal_two_mul_sub_mem k A 𝔪 s hmax hnodal t a c hspan hrel)
      ε₁ ε₂ hres hne α₀ (fun h => hα₀notmem ((hker α₀).mp h)) hcondε

/-! ### The residue fields of a finite-type algebra over an algebraically closed field -/

/-- **Zariski's lemma at a localization.** Over an algebraically closed field `k`, the residue
field of the localization of a finite-type `k`-algebra `A` at a maximal ideal is `k` itself.

The composite `A → A_𝔪 → ResidueField A_𝔪` is surjective
(`Ideal.algebraMap_residueField_surjective`), so the residue field is of finite type over `k`;
being a field, it is then finite over `k` by the Nullstellensatz, hence integral, and an integral
extension of an algebraically closed field is trivial.

This discharges the rationality hypothesis of
`Stacks.Curves.exists_branchResidues_of_isNodalAlgebra`, whose branch residues take values in
`k`. -/
public theorem nonempty_residueField_localization_algEquiv_of_isAlgClosed (k : Type u) (A : Type v)
    [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A)
    [𝔪.IsMaximal] :
    Nonempty (ResidueField (Localization.AtPrime 𝔪) ≃ₐ[k] k) := by
  have : Algebra.FiniteType k (ResidueField (Localization.AtPrime 𝔪)) :=
    Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom k A (ResidueField (Localization.AtPrime 𝔪)))
      (Ideal.algebraMap_residueField_surjective 𝔪)
  have : Module.Finite k (ResidueField (Localization.AtPrime 𝔪)) :=
    finite_of_finite_type_of_isJacobsonRing k (ResidueField (Localization.AtPrime 𝔪))
  have : Algebra.IsIntegral k (ResidueField (Localization.AtPrime 𝔪)) :=
    Algebra.IsIntegral.of_finite k (ResidueField (Localization.AtPrime 𝔪))
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (ResidueField (Localization.AtPrime 𝔪)))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

/-- **Items (1), (2) and (3) of Stacks 0E68 for a finite-type algebra over an algebraically closed
field.** This is
`Stacks.Curves.existsUnique_extend_integralClosure_branchResidues_of_isNodalAlgebra` with its
hypothesis that the residue field at each node be `k` discharged by Zariski's lemma, in the form
`Stacks.Curves.nonempty_residueField_localization_algEquiv_of_isAlgClosed`.

Every hypothesis that remains is about the node locus: the `𝔪ᵢ` are finitely many distinct maximal
ideals, each a node, every other maximal ideal is regular, and every minimal prime lies under one
of the nodes. The last cannot be dropped — on `A = k[x]`, with no nodes at all, item (1) is
satisfied by `t = 0`, `a = c = 0` and `2 t - c = 0` vanishes everywhere. -/
public theorem existsUnique_extend_integralClosure_branchResidues_of_finiteType (k : Type u)
    (A : Type v) [Field k] [IsAlgClosed k] [CommRing A] [IsReduced A] [Ring.KrullDimLE 1 A]
    [Algebra k A] [Algebra.FiniteType k A] (hNagata : IsNagataRing A) {ι : Type*}
    (𝔪 : ι → Ideal A) (s : Finset ι)
    (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔪 i ≠ 𝔪 j)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], (∀ i ∈ s, 𝔪 i ≠ P) →
      IsRegularLocalRing (Localization.AtPrime P))
    (hcomp : ∀ p ∈ minimalPrimes A, ∃ i ∈ s, p ≤ 𝔪 i) :
    ∀ i ∈ s, ∃ (t : ↥(integralClosure A (FractionRing A))) (a c : A)
      (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k),
      Algebra.adjoin A ({(t : FractionRing A)} : Set (FractionRing A)) =
          integralClosure A (FractionRing A) ∧
        t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
            algebraMap A ↥(integralClosure A (FractionRing A)) c * t ∧
          (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
              ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) b)) ∧
            ε₁ t - ε₂ t = 1 ∧
              (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) = 0 ↔
                  b ∈ 𝔪 i) ∧
                ∀ D : Derivation k A A,
                  ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
                      ↥(integralClosure A (FractionRing A)),
                    (∀ b : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
                        algebraMap A ↥(integralClosure A (FractionRing A)) (D b)) ∧
                      (∀ z, ε₁ (D' z) = 0) ∧ (∀ z, ε₂ (D' z) = 0) :=
  existsUnique_extend_integralClosure_branchResidues_of_isNodalAlgebra k A hNagata 𝔪 s hmax
    hdistinct hnodal hreg hcomp
    fun P _ _ => nonempty_residueField_localization_algEquiv_of_isAlgClosed k A P

end Stacks.Curves

end
