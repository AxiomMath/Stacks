module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAssembly

/-!
# Reducing the finite case of property (B) to a single étale covering

The ring-theoretic statement `Stacks.EtaleCohomology.HasFiniteCaseDecomposition` that the finite
case of property (B), [Stacks, Tag 04DQ], was reduced to in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAssembly` is phrased for a
*family* `C : K → Type u` of étale `B`-algebras jointly covering `Spec B`, because that is the
form a refinement of a covering of a scheme comes in. The étale local structure theorem
[Stacks, Tag 00UL], in the form
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`, is applied
to a *single* étale algebra.

This file bridges the two. The single algebra is the product `∀ k, C k`, which is étale because
`K` is finite and whose spectrum surjects onto `Spec B` precisely because the family covers. The
difficulty is on the way back: a decomposition whose factors are algebras over the *product*
carries no morphism to a single member `C k`, which is what the geometric assembly
`Stacks.EtaleCohomology.hasLocalDecompositionAt_of_algEquivPi` needs — a factor must be
subordinate to one member of the covering. The remedy is to split each factor further along the
`K`-indexed idempotents of the product: a factor over `∀ k, C k` is the product of its `K` pieces
`F ⧸ (1 - e k)`, and the `k`-th piece *is* an algebra over `C k`, compatibly with `B`. The index
type of the decomposition is refined from `L` to `L × K` and the subordination map is the second
projection.

## Main definitions

* `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover` is the ring-theoretic statement of
  the finite case for a single étale `B`-algebra `C` with `Spec C → Spec B` surjective.

## Main results

* `Stacks.EtaleCohomology.surjective_comap_algebraMap_pi`: the spectrum of the product of a
  finite family of algebras jointly covering `Spec B` surjects onto `Spec B`.
* `Stacks.EtaleCohomology.exists_pi_algEquiv_of_algebra_pi`: **an algebra over a finite product
  splits along the factors.** An algebra `T` over `∀ k, C k` is, as a `B`-algebra, the product of
  `K` rings, the `k`-th of which is an algebra over `C k` compatibly with `B`.
* `Stacks.EtaleCohomology.notMem_map_algebraMap_comp_of_notMem`: an element outside a prime of
  the base stays outside the prime that a prime above it cuts out in a localisation.
* `Stacks.EtaleCohomology.etale_of_isLocalizationAway_of_etale`: a shrinking of an étale base is
  still étale.
* `Stacks.EtaleCohomology.exists_notMem_isLocalizationAway_mul`: **the element of a second
  shrinking pushed back to the original base.** A localisation of `A'[1/a₁]` away from one element
  is a localisation of `A'` away from one element.
* `Stacks.EtaleCohomology.tensorLocalizationAwayEquivLeft`: `B ⊗[A] A'[1/a]` is `(A' ⊗[A] B)[1/a]`,
  as `B`-algebras.
* `Stacks.EtaleCohomology.hasFiniteCaseDecomposition_of_cover`:
  `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover` implies
  `Stacks.EtaleCohomology.HasFiniteCaseDecomposition`, hence — through
  `Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition` and
  `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_hasFiniteCaseDecomposition` — the
  finite and integral cases of property (B).

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

universe u

namespace Stacks.EtaleCohomology

open TensorProduct

section PiCover

/-- **The spectrum of the product of a jointly covering family surjects onto the base.** If every
prime of `B` is in the image of `Spec (C k) → Spec B` for some `k`, and there are finitely many
`k`, then `Spec (∀ k, C k) → Spec B` is surjective.

The prime of the product over a given prime `q` of `B` is the contraction along the `k`-th
projection of a prime of `C k` above `q`. This is the hypothesis `hsurj` of
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange` obtained from
the joint-covering hypothesis of
`Stacks.EtaleCohomology.HasFiniteCaseDecomposition`. -/
theorem surjective_comap_algebraMap_pi {B : Type u} [CommRing B] {K : Type u} (C : K → Type u)
    [∀ k, CommRing (C k)] [∀ k, Algebra B (C k)]
    (hcov : ∀ q : PrimeSpectrum B, ∃ k, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (C k)))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (∀ k, C k))) := by
  intro q
  obtain ⟨k, r, hr⟩ := hcov q
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun k => C k) k) r, ?_⟩
  rwa [← PrimeSpectrum.comap_comp_apply]

end PiCover

section PiSplit

variable {B : Type u} [CommRing B] {K : Type u}

/-- **Multiplying by an idempotent does not change the class modulo its complement.** In
`T ⧸ (1 - e)` the class of `y * e` is the class of `y`, because `y * e - y = -y * (1 - e)`.

This is why the quotient `T ⧸ (1 - e)` — the factor of `T` cut out by the idempotent `e` — is an
algebra over the `e`-component of a ring acting on `T`: the structure map is `c ↦ [e · c]`, and
this lemma is what makes it unital and compatible with the base. -/
theorem quotientMk_mul_eq_quotientMk (T : Type*) [CommRing T] (e y : T) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) (y * e) =
      Ideal.Quotient.mk (Ideal.span {1 - e}) y := by
  rw [Ideal.Quotient.eq, show y * e - y = (-y) * (1 - e) by ring]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable (C : K → Type u) [∀ k, CommRing (C k)]

/-- **The structure map of the `k`-th factor of an algebra over a finite product.** Let `T` be an
algebra over `∀ j, C j` and let `e k` be the image in `T` of the `k`-th standard idempotent
`Pi.single k 1`. The factor `T ⧸ (1 - e k)` is a `C k`-algebra via `c ↦ [Pi.single k c]`.

Multiplicativity is `Pi.single_mul`, and unitality is
`Stacks.EtaleCohomology.quotientMk_mul_eq_quotientMk`: the image of `Pi.single k 1` is `e k`,
whose class modulo `1 - e k` is `1`. This is the morphism to a *single member* of the covering
that the geometric assembly of the finite case of property (B), [Stacks, Tag 04DQ], requires and
that an algebra structure over the product does not supply. -/
noncomputable def piFactorAlgebraMap [DecidableEq K] (T : Type u) [CommRing T]
    [Algebra (∀ j, C j) T] (k : K) :
    C k →+* T ⧸ Ideal.span {1 - algebraMap (∀ j, C j) T (Pi.single k 1)} where
  toFun c := Ideal.Quotient.mk _ (algebraMap (∀ j, C j) T (Pi.single k c))
  map_one' := by
    have h : Ideal.Quotient.mk
        (Ideal.span {1 - algebraMap (∀ j, C j) T (Pi.single k (1 : C k))})
        (1 * algebraMap (∀ j, C j) T (Pi.single k (1 : C k))) = 1 := by
      rw [quotientMk_mul_eq_quotientMk, map_one]
    rwa [one_mul] at h
  map_mul' c₁ c₂ := by rw [Pi.single_mul, map_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero, map_zero]
  map_add' c₁ c₂ := by rw [Pi.single_add, map_add, map_add]

variable [∀ k, Algebra B (C k)]

/-- **The `k`-th factor map is compatible with the base.** The structure map
`Stacks.EtaleCohomology.piFactorAlgebraMap` of the `k`-th factor of an algebra `T` over
`∀ j, C j`, precomposed with `B → C k`, is the structure map of `T ⧸ (1 - e k)` over `B`.

The two differ by multiplication by `e k`, because the image of `b : B` in the product is the
constant vector while the factor map sees only its `k`-th entry; and multiplying by `e k` does
nothing modulo `1 - e k`, by
`Stacks.EtaleCohomology.quotientMk_mul_eq_quotientMk`. This is the scalar tower
`B → C k → T ⧸ (1 - e k)` that makes the `k`-th piece *subordinate* to the `k`-th member of the
covering in the finite case of property (B), [Stacks, Tag 04DQ]. -/
theorem piFactorAlgebraMap_algebraMap [DecidableEq K] (T : Type u) [CommRing T] [Algebra B T]
    [Algebra (∀ j, C j) T] [IsScalarTower B (∀ j, C j) T] (k : K) (b : B) :
    piFactorAlgebraMap C T k (algebraMap B (C k) b) =
      Ideal.Quotient.mk _ (algebraMap B T b) := by
  have key : (fun j => algebraMap B (C j) b) * Pi.single k (1 : C k)
      = Pi.single k (algebraMap B (C k) b) := by
    funext j
    by_cases h : k = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne' h]
  change Ideal.Quotient.mk _ (algebraMap (∀ j, C j) T (Pi.single k (algebraMap B (C k) b))) = _
  rw [← key, map_mul, quotientMk_mul_eq_quotientMk]
  exact congrArg _ (IsScalarTower.algebraMap_apply B (∀ j, C j) T b).symm

/-- **An algebra over a finite product of algebras splits along the factors.** Let `C : K → Type u`
be a finite family of `B`-algebras and let `T` be an algebra over the product `∀ k, C k`,
compatibly with `B`. Then `T` is, as a `B`-algebra, a product of `K` rings, the `k`-th of which is
an algebra over `C k` compatibly with `B`.

The `k`-th piece is `T ⧸ (1 - e k)` for `e k` the image of the `k`-th standard idempotent of the
product; these idempotents are complete and orthogonal, so
`Stacks.EtaleCohomology.completeOrthogonalIdempotentsAlgEquivPi` identifies `T` with the product
of the pieces, and `Stacks.EtaleCohomology.piFactorAlgebraMap` puts the `C k`-algebra structure on
the `k`-th one.

This is the step that makes the decomposition produced by the local structure theorem subordinate
to the covering one started with in the finite case of property (B), [Stacks, Tag 04DQ]: the
factors the ring argument produces are algebras over the product `∀ k, C k` of the members of the
covering and not over any single member, so each must be split into its `K` components before the
geometric assembly `Stacks.EtaleCohomology.hasLocalDecompositionAt_of_algEquivPi` can use them. -/
theorem exists_pi_algEquiv_of_algebra_pi [Finite K] (T : Type u) [CommRing T] [Algebra B T]
    [Algebra (∀ k, C k) T] [IsScalarTower B (∀ k, C k) T] :
    ∃ (G : K → Type u) (_ : ∀ k, CommRing (G k)) (_ : ∀ k, Algebra B (G k))
      (_ : ∀ k, Algebra (C k) (G k)) (_ : ∀ k, IsScalarTower B (C k) (G k)),
      Nonempty (T ≃ₐ[B] (∀ k, G k)) := by
  classical
  cases nonempty_fintype K
  have he : CompleteOrthogonalIdempotents
      (fun k => algebraMap (∀ j, C j) T (Pi.single k 1)) :=
    (CompleteOrthogonalIdempotents.single C).map (algebraMap (∀ j, C j) T)
  let inst : ∀ k, Algebra (C k)
      (T ⧸ Ideal.span {1 - algebraMap (∀ j, C j) T (Pi.single k 1)}) :=
    fun k => (piFactorAlgebraMap C T k).toAlgebra
  exact ⟨fun k => T ⧸ Ideal.span {1 - algebraMap (∀ j, C j) T (Pi.single k 1)},
    fun k => inferInstance, fun k => inferInstance, inst,
    fun k => .of_algebraMap_eq fun b => (piFactorAlgebraMap_algebraMap C T k b).symm,
    ⟨completeOrthogonalIdempotentsAlgEquivPi (A := B) he⟩⟩

end PiSplit

section Reduction

/-- **Uncurrying a product of products of algebras.** The `L`-indexed product of the `K`-indexed
products of `G l k` is the `L × K`-indexed product, as `R`-algebras.

This is the regrouping of a decomposition indexed by `L` whose pieces are themselves decomposed
into `K` pieces into a single decomposition indexed by `L × K`, which is the index type the finite
case of property (B), [Stacks, Tag 04DQ], ends up with: `L` indexes the factors the ring argument
produces and `K` the members of the covering they must be made subordinate to. -/
def piProdAlgEquiv (R : Type*) [CommSemiring R] {L K : Type*} (G : L → K → Type*)
    [∀ l k, Semiring (G l k)] [∀ l k, Algebra R (G l k)] :
    ((l : L) → (k : K) → G l k) ≃ₐ[R] ((lk : L × K) → G lk.1 lk.2) where
  toFun x lk := x lk.1 lk.2
  invFun y l k := y (l, k)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **The ring-theoretic content of the finite case of property (B) for a single covering.** Let
`A → B` be module-finite, let `C` be an étale `B`-algebra with `Spec C → Spec B` surjective, and
let `p` be a prime of `A`. The statement asks for an étale `A`-algebra `A₁` with a prime `p₁` over
`p` such that `B ⊗[A] A₁` is a finite product of `C`-algebras, compatibly with `B`.

This is `Stacks.EtaleCohomology.HasFiniteCaseDecomposition` with the finite *family* of étale
`B`-algebras replaced by a single one. The two are equivalent — in the direction that matters,
by `Stacks.EtaleCohomology.hasFiniteCaseDecomposition_of_cover` — and this is the form in which
the étale local structure theorem [Stacks, Tag 00UL] is applied, through
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`, which takes
one étale algebra and not a family. -/
def HasFiniteCaseDecompositionOfCover : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C] [Module.Finite A B] [Algebra.Etale B C]
    (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap B C)))
    (p : Ideal A) [p.IsPrime],
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra A A₁) (_ : Algebra.Etale A A₁)
      (p₁ : Ideal A₁) (_ : p₁.IsPrime) (_ : p₁.LiesOver p)
      (L : Type u) (_ : Finite L) (F : L → Type u) (_ : ∀ l, CommRing (F l))
      (_ : ∀ l, Algebra B (F l)) (_ : ∀ l, Algebra C (F l))
      (_ : ∀ l, IsScalarTower B C (F l)),
      Nonempty ((B ⊗[A] A₁) ≃ₐ[B] (∀ l, F l))

/-- **The family form of the ring-theoretic statement follows from the single-covering form.**
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover` implies
`Stacks.EtaleCohomology.HasFiniteCaseDecomposition`.

The single covering is the product `∀ k, C k` of the members of the family: it is étale because
`K` is finite, and its spectrum surjects onto `Spec B` by
`Stacks.EtaleCohomology.surjective_comap_algebraMap_pi` precisely because the family covers. The
decomposition the single-covering form returns has factors that are algebras over the product and
hence over no single member, so each is split into its `K` components by
`Stacks.EtaleCohomology.exists_pi_algEquiv_of_algebra_pi`; the index type becomes `L × K`, the
subordination map `κ` is the second projection, and the pieces are regrouped by
`Stacks.EtaleCohomology.piProdAlgEquiv`. -/
theorem hasFiniteCaseDecomposition_of_cover (h : HasFiniteCaseDecompositionOfCover.{u}) :
    HasFiniteCaseDecomposition.{u} := by
  classical
  intro A B _ _ _ _ K _ C _ _ _ hcov p _
  let : Algebra A (∀ k, C k) :=
    ((algebraMap B (∀ k, C k)).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B (∀ k, C k) := .of_algebraMap_eq fun _ => rfl
  obtain ⟨A₁, _, _, _, p₁, _, _, L, _, F, hFring, hFalgB, hFalgC, hFtower, ⟨ε⟩⟩ :=
    h A B (∀ k, C k) (surjective_comap_algebraMap_pi C hcov) p
  choose G hGring hGalgB hGalgC hGtower hGequiv using fun l =>
    exists_pi_algEquiv_of_algebra_pi (B := B) C (F l)
  exact ⟨A₁, ‹_›, ‹_›, ‹_›, p₁, ‹_›, ‹_›, L × K, inferInstance, Prod.snd,
    fun lk => G lk.1 lk.2, fun lk => hGring lk.1 lk.2, fun lk => hGalgB lk.1 lk.2,
    fun lk => hGalgC lk.1 lk.2, fun lk => hGtower lk.1 lk.2,
    ⟨ε.trans ((AlgEquiv.piCongrRight fun l => (hGequiv l).some).trans (piProdAlgEquiv B G))⟩⟩

end Reduction

section Shrink

/-- **An element outside a prime of the base stays outside the prime a factor cuts out.** Let `E`
be a `P`-algebra, let `D` be the localisation of `E` away from `y`, let `s` be a prime of `E`
avoiding `y` and lying over a prime `t` of `P`, and let `x : P` be outside `t`. Then the image of
`x` in `D` is outside the prime of `D` cut out by `s`.

The image of `x` lies in `s.map (algebraMap E D)` exactly when its image in `E` lies in the
contraction of that ideal, which is `s` itself by
`Stacks.EtaleCohomology.under_map_algebraMap_of_notMem`; and `s` contracts to `t` in `P`.

Note that the image of `x` in `D` is written as the *composite* `P → E → D` rather than as
`algebraMap P D`: the `P`-algebra structure on `Localization.Away y` does exist, but in the
situation of the finite case of property (B), [Stacks, Tag 04DQ], where `E` is a tensor product
`(A' ⊗[A] B) ⊗[B] C`, the scalar tower `P → E → D` is not found by instance search, because the
`SMul` of `P` on `E` chosen there is `TensorProduct.leftHasSMul` and not the one the tower
instance for a localisation is stated for. Writing the composite avoids the question.

This is the hypothesis `hl₀` of
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_algebraMap_eq_one` in the per-index step of the
finite case: the idempotent `b` of the finite side avoids the chosen prime of the base, so it
avoids the prime of the factor `E[1/c]` of the covering side that sits above it, which is what
lets that factor be isolated. -/
theorem notMem_map_algebraMap_comp_of_notMem {P E D : Type*} [CommRing P] [CommRing E]
    [CommRing D] [Algebra P E] [Algebra E D] (y : E) [IsLocalization.Away y D]
    (t : Ideal P) (s : Ideal E) [s.IsPrime] [s.LiesOver t] (hy : y ∉ s) {x : P} (hx : x ∉ t) :
    ((algebraMap E D).comp (algebraMap P E)) x ∉ s.map (algebraMap E D) := by
  intro hmem
  refine hx ((Ideal.mem_of_liesOver s t x).2 ?_)
  rw [← under_map_algebraMap_of_notMem (S := D) y s hy, Ideal.mem_under]
  exact hmem

/-- **A shrinking of an étale base is still étale.** If `A'` is étale over `A` and `A₁` is the
localisation of `A'` away from one element, compatibly with `A`, then `A₁` is étale over `A`.

A localisation at one element is étale, and étaleness composes. This is why the étale
neighbourhood of the base that the finite case of property (B), [Stacks, Tag 04DQ], produces is
still étale after the shrinkings performed by the lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra`: those lemmas invert an
element of the base supplied by the étale local structure theorem [Stacks, Tag 00UL], and the
result must still be an étale `A`-algebra. -/
theorem etale_of_isLocalizationAway_of_etale {A A' A₁ : Type*} [CommRing A] [CommRing A']
    [CommRing A₁] [Algebra A A'] [Algebra A A₁] [Algebra A' A₁] [IsScalarTower A A' A₁]
    [Algebra.Etale A A'] (a : A') [IsLocalization.Away a A₁] :
    Algebra.Etale A A₁ :=
  have : Algebra.Etale A' A₁ := Algebra.Etale.of_isLocalizationAway a
  Algebra.Etale.comp A A' A₁

/-- **The element of a second shrinking is pushed back to the original base.** Let `A''` be the
localisation of `A'` away from `a₁`, let `a₂ : A''` avoid the prime of `A''` cut out by a prime
`p'` of `A'` that `a₁` avoids, and let `T` be the localisation of `A''` away from `a₂`. Then there
is an `x : A'` outside `p'` with `T` the localisation of `A'` away from `a₁ * x`.

The element `x` is a numerator of `a₂`: by `IsLocalization.surj` the element `a₂` times a power of
the image of `a₁` is the image of some `x : A'`, and that power is a unit, so `a₂` and the image
of `x` are associated and `IsLocalization.Away.mul_of_associated` applies. The element `x` is
outside `p'` because otherwise `a₂`, an associate of its image, would lie in the prime of `A''`
cut out by `p'`.

This is the push-back that the finite case of property (B), [Stacks, Tag 04DQ], needs in order to
compose two shrinkings into one: the per-index trivialisation
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair`
cannot be applied over the original base — its module-finiteness hypothesis fails there — so it is
applied over `A'[1/a₁]` and returns an element of *that* ring, while the étale neighbourhood of
the base must be a localisation of `A'` itself. -/
theorem exists_notMem_isLocalizationAway_mul {A' A'' T : Type*} [CommRing A'] [CommRing A'']
    [CommRing T] [Algebra A' A''] [Algebra A' T] [Algebra A'' T] [IsScalarTower A' A'' T]
    (p' : Ideal A') [p'.IsPrime] (a₁ : A') [IsLocalization.Away a₁ A'']
    (a₂ : A'') [IsLocalization.Away a₂ T]
    (ha₂ : a₂ ∉ p'.map (algebraMap A' A'')) :
    ∃ x ∉ p', IsLocalization.Away (a₁ * x) T := by
  obtain ⟨⟨x, m⟩, hxa⟩ := IsLocalization.surj (Submonoid.powers a₁) a₂
  have hunit : IsUnit (algebraMap A' A'' (m : A')) := IsLocalization.map_units A'' m
  have hx : a₂ = algebraMap A' A'' x * ((hunit.unit⁻¹ : A''ˣ) : A'') :=
    (Units.eq_mul_inv_iff_mul_eq _).2 (by rwa [hunit.unit_spec])
  refine ⟨x, fun hxp => ha₂ ?_,
    IsLocalization.Away.mul_of_associated (S := A'') a₁ x a₂ ⟨hunit.unit⁻¹, hx.symm⟩⟩
  rw [hx]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hxp)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **`(A' ⊗[A] B)[1/a]` as a `B`-algebra.** The localisation of the base change `A' ⊗[A] B` away
from an element `a` of `A'` is an algebra over `B` through the right tensor factor.

This is the `B`-algebra structure the decomposition produced by the ring argument of the finite
case of property (B), [Stacks, Tag 04DQ], carries: the shrinking lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra` work inside
`(A' ⊗[A] B)[1/a]`, while the decomposition the geometric assembly needs must be an equivalence of
`B`-algebras. -/
@[instance_reducible]
noncomputable def awayTensorRightAlgebra (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (a : A') :
    Algebra B (Localization.Away (algebraMap A' (A' ⊗[A] B) a)) :=
  ((algebraMap (A' ⊗[A] B) (Localization.Away (algebraMap A' (A' ⊗[A] B) a))).comp
    (algebraMap B (A' ⊗[A] B))).toAlgebra

attribute [local instance] awayTensorRightAlgebra

/-- **Inverting an element of the base commutes with base change, `B`-linearly.** For an
`A`-algebra `A'`, an `A`-algebra `B` and `a : A'`, the ring `B ⊗[A] A'[1/a]` is `(A' ⊗[A] B)[1/a]`,
as `B`-algebras.

This is `Stacks.EtaleCohomology.tensorLocalizationAwayEquiv` composed with
`Algebra.TensorProduct.commRight` and read as an equivalence of `B`-algebras rather than of
`A'[1/a]`-algebras. Both readings are needed in the finite case of property (B),
[Stacks, Tag 04DQ]: the ring argument produces a decomposition of `(A' ⊗[A] B)[1/a]`, while
`Stacks.EtaleCohomology.hasLocalDecompositionAt_of_algEquivPi` needs a decomposition of
`B ⊗[A] A₁` for the étale neighbourhood `A₁ = A'[1/a]` of the base, and it is the `B`-linearity
that makes the pieces subordinate to the covering. -/
noncomputable def tensorLocalizationAwayEquivLeft (A A' B : Type u) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] (a : A') :
    (B ⊗[A] Localization.Away a) ≃ₐ[B] Localization.Away (algebraMap A' (A' ⊗[A] B) a) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.commRight A B (Localization.Away a)).toRingEquiv.trans
      (tensorLocalizationAwayEquiv A A' B a).toRingEquiv)
    fun x => by
      change tensorLocalizationAwayEquiv A A' B a
        (Algebra.TensorProduct.commRight A B (Localization.Away a) (x ⊗ₜ[A] 1)) = _
      rw [Algebra.TensorProduct.commRight_tmul, tensorLocalizationAwayEquiv_one_tmul]
      rfl

end Shrink

end Stacks.EtaleCohomology

end
