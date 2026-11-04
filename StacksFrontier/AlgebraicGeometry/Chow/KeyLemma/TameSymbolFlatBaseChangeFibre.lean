module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFibreTransport
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeGeneral
public import StacksFrontier.RingTheory.Localization.SemilocalizationFibre

/-!
# The maximal ideals of a flat base change, fibred over the base extension

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a local homomorphism of local rings and let `A ⊆ B` be a finite
extension. The proof of Stacks 0EPG computes the tame symbol over `A'` as a product over the
maximal ideals of `B' = A' ⊗_A B`, grouped into the fibres over the maximal ideals `𝔮` of `B`:
"over each `𝔪_j` sit maximal ideals `𝔪'_{j,l}`". This file supplies that grouping.

The one fact it needs is that every maximal ideal `𝔭` of `B'` *does* lie over a maximal ideal of
`B`. That is not formal: it is because `B'` is finite over the local ring `A'`, so `𝔭` contracts
to `𝔪'` in `A'` and therefore to `𝔪` in `A`, and `B` is integral over `A`, so a prime of `B` over
`𝔪` is maximal. With the map `𝔭 ↦ 𝔭 ∩ B` in hand the grouping is the tautological fibre
decomposition of a map of finite sets.

The fibre over `𝔮` is then identified with the index set the development's form of the identity
actually produces: the maximal ideals of `A' ⊗_A B_𝔮` that contain the image of the parameter
`π_𝔮`. One inclusion is that such a maximal ideal contracts to the maximal ideal of `B_𝔮` —
because `B_𝔮 / π_𝔮 B_𝔮` is Artinian — hence to `𝔪` in `A`, hence (a power of `𝔪'` lying in
`𝔪 A'`) to `𝔪'` in `A'`, so that its contraction to `A' ⊗_A B` is maximal by integrality over
`A'`. The other is that a maximal ideal of `A' ⊗_A B` over `𝔮` extends to one of `A' ⊗_A B_𝔮`,
which `A' ⊗_A B_𝔮` being a localization of `A' ⊗_A B` supplies. The restriction to the maximal
ideals carrying `π_𝔮` is not a convenience: without it the correspondence is false, since
`A' ⊗_A B_𝔮` has maximal ideals that do not lie over `𝔮` at all.

This is the correspondence that
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeGeneral` records as missing,
where it is attributed to Stacks 0EAE. It is *not* Stacks 0EAE: that tag glues ring maps given
over the localizations at finitely many maximal ideals, the source uses it inside the proof of
Stacks 0EAG, and the list of results Stacks 0EPG cites — 0EAG, 0GU1, 0GSX, 0GSY, 0GSZ, 0GT0 —
does not contain it.

## Main definitions

* `Stacks.Chow.baseChangeUnder` — the maximal ideal of `B` below a maximal ideal of `A' ⊗_A B`.
* `Stacks.Chow.baseChangeSigmaEquiv` — the maximal ideals of `A' ⊗_A B` are the disjoint union,
  over the maximal ideals `𝔮` of `B`, of those lying over `𝔮`.
* `Stacks.Chow.baseChangeSemilocalization` — the structure map `A' ⊗_A B → A' ⊗_A B_𝔮`.
* `Stacks.Chow.baseChangeFibreEquiv` — the maximal ideals of `A' ⊗_A B_𝔮` carrying the parameter
  are the maximal ideals of `A' ⊗_A B` over `𝔮`.
* `Stacks.Chow.baseChangeSupportSigmaEquiv` — the two index sets of Stacks 0EPG, identified.

## Main results

* `Stacks.Chow.exists_maximalIdeal_pow_le_extendedMaximalIdeal` — when `A' / 𝔪A'` has finite
  length a power of `𝔪'` lies in `𝔪A'`, so an ideal containing `𝔪A'` contains `𝔪'`.
* `Stacks.Chow.isMaximal_under_baseChange` — a maximal ideal of `A' ⊗_A B` contracts to a maximal
  ideal of `B`.
* `Stacks.Chow.prod_maximalSpectrum_baseChange_eq_prod_prod` — a product over the maximal ideals
  of `A' ⊗_A B` as an iterated product over the fibres.
* `Stacks.Chow.isLocalization_baseChangeSemilocalization` — `A' ⊗_A B_𝔮` is the localization of
  `A' ⊗_A B` at the image of the complement of `𝔮`.
* `Stacks.Chow.prod_maximalSpectrum_baseChange_eq_prod_prod_support` — the index-set
  identification as an equality of products.
* `Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` — Stacks 0EPG for a general pair of
  nonzerodivisors, with hypotheses that hold in the situation of the tag.

The factors of that product are read in the local rings `(A' ⊗_A B_𝔮)_p` rather than in the
`(A' ⊗_A B)_𝔭` of the source. Carrying them across the index-set identification recorded here
turns the double product into the source's single product over `MaximalSpectrum (A' ⊗_A B)`; that
is `Stacks.Chow.map_symbolValue_pow_eq_prod_maximalSpectrum`, in
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeSingleProduct`.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A quotient `R / I` of finite length over `R` is an Artinian ring. -/
private theorem isArtinianRing_quotient_of_length_ne_top {R : Type*} [CommRing R] {I : Ideal R}
    (h : Module.length R (R ⧸ I) ≠ ⊤) : IsArtinianRing (R ⧸ I) :=
  isArtinianRing_iff.mpr (isArtinian_of_tower R
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)).2)

section Extended

variable {A : Type u} [CommRing A] [IsLocalRing A] (A' : Type v) [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')]

/-- **A power of `𝔪'` lies in `𝔪 A'`** as soon as `A' / 𝔪A'` has finite length over `A'`: that
quotient is then an Artinian local ring, so its maximal ideal — the image of `𝔪'` — is nilpotent.
Consequently a prime of an `A'`-algebra containing the image of `𝔪` contains the image of `𝔪'`,
which is how the exponent `m` of Stacks 0EPG forces the maximal ideals in play to lie over `𝔪'`. -/
theorem exists_maximalIdeal_pow_le_extendedMaximalIdeal
    (hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤) :
    ∃ N : ℕ, maximalIdeal A' ^ N ≤ extendedMaximalIdeal A A' := by
  set J := extendedMaximalIdeal A A' with hJdef
  have hJle : J ≤ maximalIdeal A' := map_maximalIdeal_le (algebraMap A A')
  have hJtop : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A').ne_top (top_le_iff.mp (h ▸ hJle))
  have : IsArtinianRing (A' ⧸ J) := isArtinianRing_quotient_of_length_ne_top hfin
  have : Nontrivial (A' ⧸ J) :=
    not_subsingleton_iff_nontrivial.mp fun h => hJtop (Ideal.Quotient.subsingleton_iff.mp h)
  have : IsLocalRing (A' ⧸ J) :=
    of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal A')).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJle)
  have heq : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal A') = maximalIdeal (A' ⧸ J) :=
    eq_maximalIdeal hmax
  obtain ⟨N, hN⟩ : IsNilpotent (maximalIdeal (A' ⧸ J)) := by
    rw [← jacobson_eq_maximalIdeal (⊥ : Ideal (A' ⧸ J)) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  refine ⟨N, ?_⟩
  have hbot : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal A' ^ N) = ⊥ := by
    rw [Ideal.map_pow, heq]
    simpa using hN
  have := (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk J)).mp hbot
  rwa [Ideal.mk_ker] at this

end Extended

section Under

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')]
  {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **A maximal ideal of `A' ⊗_A B` contracts to a maximal ideal of `B`.** The base change is
finite over `A'`, hence integral, so the contraction to `A'` is the maximal ideal `𝔪'`, whose
contraction to `A` is `𝔪`; and `B` is integral over `A`, so a prime of `B` lying over `𝔪` is
maximal. -/
theorem isMaximal_under_baseChange (𝔭 : MaximalSpectrum (A' ⊗[A] B)) :
    (𝔭.asIdeal.under B).IsMaximal := by
  have : Module.Finite A' (A' ⊗[A] B) := Module.Finite.base_change A A' B
  have : Algebra.IsIntegral A' (A' ⊗[A] B) := Algebra.IsIntegral.of_finite A' _
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : 𝔭.asIdeal.IsPrime := 𝔭.isMaximal.isPrime
  have h1 : 𝔭.asIdeal.under A' = maximalIdeal A' :=
    eq_maximalIdeal (Ideal.IsMaximal.under A' 𝔭.asIdeal)
  have h2 : (𝔭.asIdeal.under B).under A = maximalIdeal A := by
    rw [Ideal.under_under, ← Ideal.under_under (A := A) (B := A') 𝔭.asIdeal, h1]
    exact maximalIdeal_comap (algebraMap A A')
  have : (𝔭.asIdeal.under B).IsPrime := Ideal.IsPrime.under B 𝔭.asIdeal
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (𝔭.asIdeal.under B) ?_
  show ((𝔭.asIdeal.under B).under A).IsMaximal
  rw [h2]
  exact maximalIdeal.isMaximal A

/-- The maximal ideal of `B` below a maximal ideal of the flat base change `A' ⊗_A B`. -/
def baseChangeUnder (𝔭 : MaximalSpectrum (A' ⊗[A] B)) : MaximalSpectrum B :=
  ⟨𝔭.asIdeal.under B, isMaximal_under_baseChange 𝔭⟩

/-- The ideal underlying `baseChangeUnder 𝔭` is the contraction `𝔭 ∩ B` of `𝔭` to `B`. -/
@[simp]
theorem baseChangeUnder_asIdeal (𝔭 : MaximalSpectrum (A' ⊗[A] B)) :
    (baseChangeUnder 𝔭).asIdeal = 𝔭.asIdeal.under B := rfl

/-- **The fibred decomposition of the maximal spectrum of a flat base change.** The maximal ideals
of `A' ⊗_A B` are the disjoint union, over the maximal ideals `𝔮` of `B`, of those lying over
`𝔮` — the grouping the proof of Stacks 0EPG uses. -/
def baseChangeSigmaEquiv :
    (Σ q : MaximalSpectrum B, {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q}) ≃
      MaximalSpectrum (A' ⊗[A] B) :=
  Equiv.sigmaFiberEquiv baseChangeUnder

/-- `baseChangeSigmaEquiv` sends a pair `⟨𝔮, 𝔭⟩`, with `𝔭` over `𝔮`, to the maximal ideal `𝔭`. -/
@[simp]
theorem baseChangeSigmaEquiv_apply (q : MaximalSpectrum B)
    (𝔭 : {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q}) :
    baseChangeSigmaEquiv ⟨q, 𝔭⟩ = 𝔭.1 := rfl

/-- **A product over the maximal ideals of `A' ⊗_A B` as an iterated product over the fibres.** -/
theorem prod_maximalSpectrum_baseChange_eq_prod_prod {M : Type*} [CommMonoid M]
    [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum (A' ⊗[A] B))]
    [∀ q : MaximalSpectrum B,
      Fintype {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q}]
    (f : MaximalSpectrum (A' ⊗[A] B) → M) :
    ∏ 𝔭 : MaximalSpectrum (A' ⊗[A] B), f 𝔭 =
      ∏ q : MaximalSpectrum B,
        ∏ 𝔭 : {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q}, f 𝔭.1 := by
  rw [← Fintype.prod_equiv baseChangeSigmaEquiv
    (fun x => f (baseChangeSigmaEquiv x)) f fun _ => rfl]
  exact Fintype.prod_sigma _

end Under

section Semilocalization

variable (A : Type u) [CommRing A] (A' : Type v) [CommRing A'] [Algebra A A']
  {B : Type w} [CommRing B] [Algebra A B] (q : MaximalSpectrum B)

/-- The right-hand structure map of a tensor product is the inclusion of the right factor. -/
theorem algebraMap_right_eq_includeRight (b : B) :
    algebraMap B (A' ⊗[A] B) b = Algebra.TensorProduct.includeRight b := rfl

/-- **The base change of `B → B_𝔮`**: the structure map `A' ⊗_A B → A' ⊗_A B_𝔮`. -/
noncomputable def baseChangeSemilocalization :
    A' ⊗[A] B →ₐ[A] A' ⊗[A] Localization.AtPrime q.asIdeal :=
  Algebra.TensorProduct.map (AlgHom.id A A')
    (IsScalarTower.toAlgHom A B (Localization.AtPrime q.asIdeal))

/-- `baseChangeSemilocalization` sends `x ⊗ b` to `x ⊗ b/1`, where `b/1` is the image of `b` in
`B_𝔮`. -/
@[simp]
theorem baseChangeSemilocalization_tmul (x : A') (b : B) :
    baseChangeSemilocalization A A' q (x ⊗ₜ[A] b) =
      x ⊗ₜ[A] algebraMap B (Localization.AtPrime q.asIdeal) b := by
  simp [baseChangeSemilocalization]

/-- `A' ⊗_A B` acts on `A' ⊗_A B_𝔮` through the base change of `B → B_𝔮`. This is not an instance:
it is the structure under which `A' ⊗_A B_𝔮` is a localization of `A' ⊗_A B`, and the statements
that need it install it themselves. -/
@[instance_reducible]
noncomputable def baseChangeSemilocalizationAlgebra :
    Algebra (A' ⊗[A] B) (A' ⊗[A] Localization.AtPrime q.asIdeal) :=
  (baseChangeSemilocalization A A' q).toRingHom.toAlgebra

/-- Under `baseChangeSemilocalizationAlgebra`, the structure map `A' ⊗_A B → A' ⊗_A B_𝔮` is the
ring map underlying `baseChangeSemilocalization`. -/
theorem algebraMap_baseChangeSemilocalizationAlgebra :
    letI := baseChangeSemilocalizationAlgebra A A' q
    algebraMap (A' ⊗[A] B) (A' ⊗[A] Localization.AtPrime q.asIdeal) =
      (baseChangeSemilocalization A A' q).toRingHom := rfl

/-- `A' → A' ⊗_A B → A' ⊗_A B_𝔮` is a tower. -/
theorem isScalarTower_baseChangeSemilocalization :
    letI := baseChangeSemilocalizationAlgebra A A' q
    IsScalarTower A' (A' ⊗[A] B) (A' ⊗[A] Localization.AtPrime q.asIdeal) := by
  let := baseChangeSemilocalizationAlgebra A A' q
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  show _ = baseChangeSemilocalization A A' q (algebraMap A' (A' ⊗[A] B) x)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    baseChangeSemilocalization_tmul]
  simp

/-- `B → A' ⊗_A B → A' ⊗_A B_𝔮` sends `b` to `1 ⊗ b`, read in `B_𝔮`. -/
theorem baseChangeSemilocalization_includeRight (b : B) :
    baseChangeSemilocalization A A' q (Algebra.TensorProduct.includeRight b) =
      Algebra.TensorProduct.includeRight (algebraMap B (Localization.AtPrime q.asIdeal) b) := by
  simp [Algebra.TensorProduct.includeRight_apply]

/-- **`A' ⊗_A B_𝔮` is the semilocalization of `A' ⊗_A B` at `𝔮`**: it is the localization of
`A' ⊗_A B` at the image of the complement of `𝔮`. Localization commutes with the base change
`- ⊗_A A'`, which is the content of `IsLocalization.tensorProduct_tensorProduct_right`.

This is what lets the maximal ideals of `A' ⊗_A B_𝔮` — the index set of
`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support`, fibre by fibre — be compared with the
maximal ideals of `A' ⊗_A B`, which is the index set of the source's product. -/
theorem isLocalization_baseChangeSemilocalization :
    letI := baseChangeSemilocalizationAlgebra A A' q
    IsLocalization (Algebra.algebraMapSubmonoid (A' ⊗[A] B) q.asIdeal.primeCompl)
      (A' ⊗[A] Localization.AtPrime q.asIdeal) := by
  let := baseChangeSemilocalizationAlgebra A A' q
  have := isScalarTower_baseChangeSemilocalization A A' q
  have hsub : Algebra.algebraMapSubmonoid (A' ⊗[A] B) q.asIdeal.primeCompl =
      Submonoid.map
        (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B) : B →* A' ⊗[A] B)
        q.asIdeal.primeCompl := by
    ext x
    simp [Algebra.algebraMapSubmonoid, algebraMap_right_eq_includeRight,
      Algebra.TensorProduct.includeRight_apply]
  rw [hsub]
  refine IsLocalization.tensorProduct_tensorProduct_right A A' q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) ?_
  ext b
  exact baseChangeSemilocalization_includeRight A A' q b

end Semilocalization

section FibreCorrespondence

/-- **A prime containing `π` is maximal when `R / πR` is Artinian.** -/
theorem isMaximal_of_mem_of_isArtinianRing_quotient {R : Type*} [CommRing R] {π : R}
    (hart : IsArtinianRing (R ⧸ Ideal.span {π})) (P : Ideal R) [P.IsPrime] (hP : π ∈ P) :
    P.IsMaximal := by
  have := hart
  have hsub : Ideal.span {π} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hP
  have : (Ideal.map (Ideal.Quotient.mk (Ideal.span {π})) P).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hsub)
  have : (Ideal.map (Ideal.Quotient.mk (Ideal.span {π})) P).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime _
  have h : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {π}))
      (Ideal.map (Ideal.Quotient.mk (Ideal.span {π})) P)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hsub] at h

/-- `R / πR` is Artinian for a nonzerodivisor `π` of a one-dimensional Noetherian local ring. -/
theorem isArtinianRing_quotient_span {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] {π : R} (hπ : π ∈ nonZeroDivisors R) :
    IsArtinianRing (R ⧸ Ideal.span {π}) :=
  isArtinianRing_quotient_of_length_ne_top (Ring.ord_ne_top hπ)

variable (A : Type u) [CommRing A] [IsLocalRing A] (A' : Type v) [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')]
  {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B] (q : MaximalSpectrum B)

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- `B → A' ⊗_A B → A' ⊗_A B_𝔮` and `B → B_𝔮 → A' ⊗_A B_𝔮` are the same map. -/
theorem baseChangeSemilocalization_comp_algebraMap :
    (baseChangeSemilocalization A A' q).toRingHom.comp (algebraMap B (A' ⊗[A] B)) =
      (algebraMap (Localization.AtPrime q.asIdeal)
          (A' ⊗[A] Localization.AtPrime q.asIdeal)).comp
        (algebraMap B (Localization.AtPrime q.asIdeal)) := by
  ext b
  show baseChangeSemilocalization A A' q (algebraMap B (A' ⊗[A] B) b) = _
  rw [algebraMap_right_eq_includeRight, baseChangeSemilocalization_includeRight,
    RingHom.comp_apply, algebraMap_right_eq_includeRight]

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- **A maximal ideal of `A' ⊗_A B_𝔮` carrying `π` contracts to the maximal ideal of `B_𝔮`.** The
contraction is a prime containing `π`, and `B_𝔮 / πB_𝔮` is Artinian. -/
theorem under_eq_maximalIdeal_of_mem
    {π : Localization.AtPrime q.asIdeal}
    (hart : IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π}))
    (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))
    (hp : (Algebra.TensorProduct.includeRight π :
      A' ⊗[A] Localization.AtPrime q.asIdeal) ∈ p.asIdeal) :
    p.asIdeal.under (Localization.AtPrime q.asIdeal) =
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
  have : p.asIdeal.IsPrime := p.isMaximal.isPrime
  have : (p.asIdeal.under (Localization.AtPrime q.asIdeal)).IsPrime :=
    Ideal.IsPrime.under _ p.asIdeal
  have hmem : π ∈ p.asIdeal.under (Localization.AtPrime q.asIdeal) := by
    show algebraMap (Localization.AtPrime q.asIdeal) _ π ∈ p.asIdeal
    rwa [algebraMap_right_eq_includeRight]
  exact eq_maximalIdeal (isMaximal_of_mem_of_isArtinianRing_quotient hart _ hmem)

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- **The contraction to `B` of a maximal ideal of `A' ⊗_A B_𝔮` carrying `π` is `𝔮`.** -/
theorem under_comap_baseChangeSemilocalization
    {π : Localization.AtPrime q.asIdeal}
    (hart : IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π}))
    (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))
    (hp : (Algebra.TensorProduct.includeRight π :
      A' ⊗[A] Localization.AtPrime q.asIdeal) ∈ p.asIdeal) :
    (Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal).under B = q.asIdeal := by
  have hP := under_eq_maximalIdeal_of_mem A A' q hart p hp
  show Ideal.comap (algebraMap B (A' ⊗[A] B))
    (Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal) = q.asIdeal
  rw [Ideal.comap_comap, baseChangeSemilocalization_comp_algebraMap, ← Ideal.comap_comap]
  show (p.asIdeal.under (Localization.AtPrime q.asIdeal)).under B = q.asIdeal
  rw [hP]
  exact IsLocalization.AtPrime.under_maximalIdeal _ q.asIdeal

/-- **A maximal ideal of `A' ⊗_A B_𝔮` carrying `π` contracts to a maximal ideal of `A' ⊗_A B`.**
Its contraction to `B_𝔮` is the maximal ideal, so its contraction to `A` is `𝔪`; a power of `𝔪'`
lies in `𝔪A'`, so its contraction to `A'` is `𝔪'`; and `A' ⊗_A B` is integral over `A'`, so a
prime over `𝔪'` is maximal. -/
theorem isMaximal_comap_baseChangeSemilocalization
    (hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤)
    {π : Localization.AtPrime q.asIdeal}
    (hart : IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π}))
    (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))
    (hp : (Algebra.TensorProduct.includeRight π :
      A' ⊗[A] Localization.AtPrime q.asIdeal) ∈ p.asIdeal) :
    (Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal).IsMaximal := by
  let := baseChangeSemilocalizationAlgebra A A' q
  have := isScalarTower_baseChangeSemilocalization A A' q
  have : Module.Finite A' (A' ⊗[A] B) := Module.Finite.base_change A A' B
  have : Algebra.IsIntegral A' (A' ⊗[A] B) := Algebra.IsIntegral.of_finite A' _
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : p.asIdeal.IsPrime := p.isMaximal.isPrime
  have := q.isMaximal
  have : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
    isLocalHom_algebraMap_localizationAtPrime q.asIdeal
  have hP := under_eq_maximalIdeal_of_mem A A' q hart p hp
  -- the contraction to `A` contains `𝔪`
  have hmA : maximalIdeal A ≤ p.asIdeal.under A := by
    intro x hx
    have h1 : algebraMap A (Localization.AtPrime q.asIdeal) x ∈
        p.asIdeal.under (Localization.AtPrime q.asIdeal) := by
      rw [hP, ← maximalIdeal_comap (algebraMap A (Localization.AtPrime q.asIdeal))] at *
      exact hx
    show algebraMap A (A' ⊗[A] Localization.AtPrime q.asIdeal) x ∈ p.asIdeal
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal)
      (A' ⊗[A] Localization.AtPrime q.asIdeal)]
    exact h1
  -- the contraction to `A'` contains `𝔪'`
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_extendedMaximalIdeal A' hfin
  have hmap : Ideal.map (algebraMap A' (A' ⊗[A] Localization.AtPrime q.asIdeal))
      (extendedMaximalIdeal A A') ≤ p.asIdeal := by
    rw [extendedMaximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq A A' (A' ⊗[A] Localization.AtPrime q.asIdeal)]
    exact Ideal.map_le_iff_le_comap.mpr hmA
  have hmA' : maximalIdeal A' ≤ p.asIdeal.under A' := by
    intro x hx
    have hxN : x ^ N ∈ extendedMaximalIdeal A A' := hN (Ideal.pow_mem_pow hx N)
    have h2 : (algebraMap A' (A' ⊗[A] Localization.AtPrime q.asIdeal) x) ^ N ∈ p.asIdeal := by
      rw [← map_pow]
      exact hmap (Ideal.mem_map_of_mem _ hxN)
    exact ‹p.asIdeal.IsPrime›.mem_of_pow_mem N h2
  have : (p.asIdeal.under A').IsPrime := Ideal.IsPrime.under _ p.asIdeal
  have hA' : p.asIdeal.under A' = maximalIdeal A' :=
    ((maximalIdeal.isMaximal A').eq_of_le ‹(p.asIdeal.under A').IsPrime›.ne_top hmA').symm
  -- conclude by integrality over `A'`
  have : (Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal).IsPrime :=
    Ideal.IsPrime.comap _
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A')
    (Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal) ?_
  show ((Ideal.under (A' ⊗[A] B) p.asIdeal).under A').IsMaximal
  rw [Ideal.under_under, hA']
  exact maximalIdeal.isMaximal A'

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- **A maximal ideal of `A' ⊗_A B` over `𝔮` extends to a maximal ideal of `A' ⊗_A B_𝔮`.** It is
prime there because it is disjoint from the inverted set, and maximal because a prime above it
contracts to a prime above it in `A' ⊗_A B`, hence to itself. -/
theorem isMaximal_map_baseChangeSemilocalization
    (𝔭 : MaximalSpectrum (A' ⊗[A] B)) (h𝔭 : 𝔭.asIdeal.under B = q.asIdeal) :
    (Ideal.map (baseChangeSemilocalization A A' q).toRingHom 𝔭.asIdeal).IsMaximal := by
  let := baseChangeSemilocalizationAlgebra A A' q
  have := isScalarTower_baseChangeSemilocalization A A' q
  have := isLocalization_baseChangeSemilocalization A A' q
  have : 𝔭.asIdeal.IsPrime := 𝔭.isMaximal.isPrime
  have hdisj := IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq
    (R := B) (T := A' ⊗[A] B) q.asIdeal h𝔭
  have hprime : (Ideal.map (baseChangeSemilocalization A A' q).toRingHom 𝔭.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid (A' ⊗[A] B) q.asIdeal.primeCompl)
      (A' ⊗[A] Localization.AtPrime q.asIdeal) 𝔭.asIdeal inferInstance hdisj
  refine ⟨⟨hprime.ne_top, fun J hJ => ?_⟩⟩
  by_contra hJtop
  obtain ⟨P, hPmax, hPJ⟩ := Ideal.exists_le_maximal J hJtop
  have := hPmax
  have : P.IsPrime := hPmax.isPrime
  have : (P.under (A' ⊗[A] B)).IsPrime := Ideal.IsPrime.under _ P
  have hle : 𝔭.asIdeal ≤ P.under (A' ⊗[A] B) :=
    Ideal.map_le_iff_le_comap.mp (le_trans hJ.le hPJ)
  have heq : P.under (A' ⊗[A] B) = 𝔭.asIdeal :=
    (𝔭.isMaximal.eq_of_le ‹(P.under (A' ⊗[A] B)).IsPrime›.ne_top hle).symm
  have hPeq : P = Ideal.map (baseChangeSemilocalization A A' q).toRingHom 𝔭.asIdeal := by
    rw [← heq]
    exact (IsLocalization.map_under (Algebra.algebraMapSubmonoid (A' ⊗[A] B)
      q.asIdeal.primeCompl) (A' ⊗[A] Localization.AtPrime q.asIdeal) P).symm
  exact absurd (lt_of_lt_of_le hJ hPJ) (by rw [hPeq]; exact lt_irrefl _)

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- **The extension of a maximal ideal over `𝔮` carries the parameter.** The maximal ideal of
`B_𝔮` is generated by the image of `𝔮`, which lands inside every maximal ideal of `A' ⊗_A B`
over `𝔮`. -/
theorem includeRight_mem_map_baseChangeSemilocalization
    {π : Localization.AtPrime q.asIdeal}
    (hπ : π ∈ maximalIdeal (Localization.AtPrime q.asIdeal))
    (𝔭 : MaximalSpectrum (A' ⊗[A] B)) (h𝔭 : 𝔭.asIdeal.under B = q.asIdeal) :
    (Algebra.TensorProduct.includeRight π : A' ⊗[A] Localization.AtPrime q.asIdeal) ∈
      Ideal.map (baseChangeSemilocalization A A' q).toRingHom 𝔭.asIdeal := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hπ
  have hqle : Ideal.map (algebraMap B (A' ⊗[A] B)) q.asIdeal ≤ 𝔭.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq h𝔭.symm)
  refine Ideal.map_mono hqle ?_
  rw [Ideal.map_map, baseChangeSemilocalization_comp_algebraMap, ← Ideal.map_map]
  rw [← algebraMap_right_eq_includeRight A A' π]
  exact Ideal.mem_map_of_mem _ hπ

/-- **The index-set identification of Stacks 0EPG.** For a maximal ideal `𝔮` of `B` and a
parameter `π` in the maximal ideal of `B_𝔮` with `B_𝔮 / πB_𝔮` Artinian, the maximal ideals of
`A' ⊗_A B_𝔮` carrying `π` — the index set of the inner product of
`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` — are exactly the maximal ideals of
`A' ⊗_A B` lying over `𝔮`, which is the fibre of the source's index set.

Composed with `Stacks.Chow.baseChangeSigmaEquiv` this identifies the double index set of that
theorem with `MaximalSpectrum (A' ⊗_A B)`, the index set of the source's product. -/
noncomputable def baseChangeFibreEquiv
    (hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤)
    {π : Localization.AtPrime q.asIdeal}
    (hart : IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π}))
    (hπ : π ∈ maximalIdeal (Localization.AtPrime q.asIdeal)) :
    Stacks.Length.tensorSupport A A' π ≃
      {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q} where
  toFun p :=
    ⟨⟨Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.1.asIdeal,
        isMaximal_comap_baseChangeSemilocalization A A' q hfin hart p.1 p.2⟩,
      MaximalSpectrum.ext (under_comap_baseChangeSemilocalization A A' q hart p.1 p.2)⟩
  invFun 𝔭 :=
    ⟨⟨Ideal.map (baseChangeSemilocalization A A' q).toRingHom 𝔭.1.asIdeal,
        isMaximal_map_baseChangeSemilocalization A A' q 𝔭.1
          (congrArg MaximalSpectrum.asIdeal 𝔭.2)⟩,
      includeRight_mem_map_baseChangeSemilocalization A A' q hπ 𝔭.1
        (congrArg MaximalSpectrum.asIdeal 𝔭.2)⟩
  left_inv p := by
    let := baseChangeSemilocalizationAlgebra A A' q
    have := isScalarTower_baseChangeSemilocalization A A' q
    have := isLocalization_baseChangeSemilocalization A A' q
    exact Subtype.ext (MaximalSpectrum.ext
      (IsLocalization.map_under (Algebra.algebraMapSubmonoid (A' ⊗[A] B) q.asIdeal.primeCompl)
        (A' ⊗[A] Localization.AtPrime q.asIdeal) p.1.asIdeal))
  right_inv 𝔭 := by
    let := baseChangeSemilocalizationAlgebra A A' q
    have := isScalarTower_baseChangeSemilocalization A A' q
    have := isLocalization_baseChangeSemilocalization A A' q
    have : 𝔭.1.asIdeal.IsPrime := 𝔭.1.isMaximal.isPrime
    exact Subtype.ext (MaximalSpectrum.ext
      (IsLocalization.under_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid (A' ⊗[A] B) q.asIdeal.primeCompl)
        (A' ⊗[A] Localization.AtPrime q.asIdeal) inferInstance
        (IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq (R := B) (T := A' ⊗[A] B)
          q.asIdeal (congrArg MaximalSpectrum.asIdeal 𝔭.2))))

/-- **The index set of Stacks 0EPG, identified.** Given a parameter `π_𝔮` in the maximal ideal of
`B_𝔮` with `B_𝔮 / π_𝔮 B_𝔮` Artinian for each maximal ideal `𝔮` of `B`, the double index set of
`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` — pairs of a maximal ideal `𝔮` of `B` and a
maximal ideal of `A' ⊗_A B_𝔮` carrying `π_𝔮` — is the set of maximal ideals of `A' ⊗_A B`, which
is the index set of the source's product.

This is `Stacks.Chow.baseChangeFibreEquiv` in each fibre followed by
`Stacks.Chow.baseChangeSigmaEquiv`. -/
noncomputable def baseChangeSupportSigmaEquiv
    (hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤)
    {π : ∀ q : MaximalSpectrum B, Localization.AtPrime q.asIdeal}
    (hart : ∀ q : MaximalSpectrum B,
      IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π q}))
    (hπ : ∀ q : MaximalSpectrum B, π q ∈ maximalIdeal (Localization.AtPrime q.asIdeal)) :
    (Σ q : MaximalSpectrum B, Stacks.Length.tensorSupport A A' (π q)) ≃
      MaximalSpectrum (A' ⊗[A] B) :=
  (Equiv.sigmaCongrRight fun q => baseChangeFibreEquiv A A' q hfin (hart q) (hπ q)).trans
    baseChangeSigmaEquiv

/-- **The product over the maximal ideals of `A' ⊗_A B` as the double product of Stacks 0EPG.**
This is the index-set identification in the form the comparison of
`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` with the source's single product uses. -/
theorem prod_maximalSpectrum_baseChange_eq_prod_prod_support {M : Type*} [CommMonoid M]
    (hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤)
    {π : ∀ q : MaximalSpectrum B, Localization.AtPrime q.asIdeal}
    (hart : ∀ q : MaximalSpectrum B,
      IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π q}))
    (hπ : ∀ q : MaximalSpectrum B, π q ∈ maximalIdeal (Localization.AtPrime q.asIdeal))
    [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum (A' ⊗[A] B))]
    [∀ q : MaximalSpectrum B, Fintype (Stacks.Length.tensorSupport A A' (π q))]
    (f : MaximalSpectrum (A' ⊗[A] B) → M) :
    ∏ 𝔭 : MaximalSpectrum (A' ⊗[A] B), f 𝔭 =
      ∏ q : MaximalSpectrum B, ∏ p : Stacks.Length.tensorSupport A A' (π q),
        f (baseChangeSupportSigmaEquiv A A' hfin hart hπ ⟨q, p⟩) := by
  rw [← Fintype.prod_equiv (baseChangeSupportSigmaEquiv A A' hfin hart hπ)
    (fun x => f (baseChangeSupportSigmaEquiv A A' hfin hart hπ x)) f fun _ => rfl]
  exact Fintype.prod_sigma _

end FibreCorrespondence

section Support

/-- **Stacks 0EPG at a single maximal ideal, over the support.** The hypotheses are those of
`Stacks.Chow.map_norm_factorizationValue_pow_eq_prod` with the locality of `A' → (A' ⊗_A B)_𝔭`
and the finiteness of `κ(𝔭) / κ'` asked for only at the maximal ideals `𝔭` containing the image
of `π` — which is where they hold, and where the source's product runs.

The identity is `Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_support`, which is the
determinant identity Stacks 0GU1: the factor of Stacks 0EAQ is the residue of the unit
`w = (-1)^{ef} u^f v^{-e}` raised to `length_B(B / πB)`, and the exponent over `(A' ⊗_A B)_𝔭` is
the length of the corresponding quotient there. -/
theorem map_norm_factorizationValue_pow_eq_prod_support
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A']
    [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    {B : Type w} [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Ring.KrullDimLE 1 B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Finite (ResidueField A) (ResidueField B)]
    {π : B} (hπ : π ∈ nonZeroDivisors B)
    [Fintype (Stacks.Length.tensorSupport A A' π)]
    [∀ p : Stacks.Length.tensorSupport A A' π,
      IsLocalHom (algebraMap A' (Localization.AtPrime p.1.asIdeal))]
    [∀ p : Stacks.Length.tensorSupport A A' π,
      Module.Finite (ResidueField A') (ResidueField (Localization.AtPrime p.1.asIdeal))]
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m) (u v : Bˣ) (e f : ℕ) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (Units.map (Algebra.norm (ResidueField A) : ResidueField B →* ResidueField A)
          (factorizationValue π u v e f)) ^ m =
      ∏ p : Stacks.Length.tensorSupport A A' π,
        Units.map (Algebra.norm (ResidueField A') :
            ResidueField (Localization.AtPrime p.1.asIdeal) →* ResidueField A')
          (factorizationValue (baseChangeLocalizationHom A' p.1 π)
            (Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom u)
            (Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom v) e f) := by
  have hM : IsFiniteLength B (B ⧸ Ideal.span {π}) :=
    Module.length_ne_top_iff.mp (Ring.ord_ne_top hπ)
  have hkey := Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_support
    (A := A) (S := A') (B := B) π (((-1) ^ (e * f) * u ^ f * (v ^ e)⁻¹ : Bˣ) : B) hM hm
  have hright (p : Stacks.Length.tensorSupport A A' π) :
      ((-1) ^ (e * f) * (Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom u) ^ f *
          ((Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom v) ^ e)⁻¹) =
        Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom
          ((-1) ^ (e * f) * u ^ f * (v ^ e)⁻¹) := by
    have hneg : Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom (-1 : Bˣ) =
        (-1 : (Localization.AtPrime p.1.asIdeal)ˣ) := Units.ext (by simp)
    simp only [map_mul, map_pow, map_inv, hneg]
  refine Units.ext ?_
  simp only [factorizationValue_eq_units_map_residue, hright]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, map_pow, Ring.ord, baseChangeLocalizationHom_apply]
  simp only [map_pow] at hkey
  exact hkey.trans (Finset.prod_congr rfl fun i _ => rfl)

section General

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A']
  [IsLocalHom (algebraMap A A')] [Module.Flat A A']
  {B : Type w} [CommRing B] [Algebra A B]
  [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B,
    Module.Finite (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal))]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- **Stacks 0EPG for a general pair of nonzerodivisors, over the supports.** Let
`(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian local rings
and let `m = length_{A'}(A' / 𝔪A')`. Let `A ⊆ B` be a finite extension carrying a tame-symbol
preparation of a family `a` of elements of `A` — by Stacks 0EAG one exists for *every* pair of
nonzerodivisors of `A`. Then the value of the formula Stacks 0EAQ for two members of that family,
raised to the power `m` and read in `κ'`, is the value of the same formula over `A'` for the
base-changed data:

`(∏_𝔮 Norm_{κ(𝔮)/κ}(c_𝔮))^m = ∏_𝔮 ∏_𝔭 Norm_{κ(𝔭)/κ'}(c_𝔭)`,

where `𝔮` runs over the maximal ideals of `B` and `𝔭` over the maximal ideals of `A' ⊗_A B_𝔮`
containing the image of the parameter `π_𝔮`.

This differs from `Stacks.Chow.map_symbolValue_pow_eq_prod_prod` only in asking for the locality
of `A' → (A' ⊗_A B_𝔮)_𝔭` and the finiteness of `κ(𝔭) / κ'` at those `𝔭` alone, and that is the
difference between a statement that applies and one that does not. At a maximal ideal of
`A' ⊗_A B_𝔮` where the image of `π_𝔮` is a unit the local ring need not be local over `A'`, and
such maximal ideals do occur: for `A = ℤ_(5)`, `A' = ℤ₅`, `B` the semilocalization of `ℤ[i]` at
`5` and `𝔮` one of the two maximal ideals of `B`, the ring `A' ⊗_A B_𝔮` is `ℚ₅ × ℤ₅`, whose local
ring at `0 × ℤ₅` is `ℚ₅`, over which `ℤ₅` is not local.

Each factor is `Stacks.Chow.map_norm_factorizationValue_pow_eq_prod_support`, which is the
determinant identity Stacks 0GU1; the only other ingredient is that `κ → κ'` is multiplicative. -/
@[stacks 0EPG "for a general pair of nonzerodivisors, in the spelling in which both sides are \
the formula Stacks 0EAQ: on the left for a tame-symbol preparation over a finite extension `B` \
of `A`, which Stacks 0EAG provides for every pair, and on the right for the base change of that \
preparation, with the maximal ideals of the base change presented fibre by fibre over those of \
`B` and, in each fibre, as those carrying the parameter"]
theorem map_symbolValue_pow_eq_prod_prod_support
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    [∀ q : MaximalSpectrum B,
      Fintype (Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal))]
    [∀ (q : MaximalSpectrum B) (p : Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal)),
      IsLocalHom (algebraMap A' (Localization.AtPrime p.1.asIdeal))]
    [∀ (q : MaximalSpectrum B) (p : Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal)),
      Module.Finite (ResidueField A') (ResidueField (Localization.AtPrime p.1.asIdeal))] :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom (P.symbolValue i j) ^ m =
      ∏ q : MaximalSpectrum B,
        ∏ p : Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal),
          Units.map (Algebra.norm (ResidueField A') :
              ResidueField (Localization.AtPrime p.1.asIdeal) →* ResidueField A')
            (factorizationValue (baseChangeLocalizationHom A' p.1 (P.parameter q.asIdeal))
              (Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom
                (P.factorUnit q.asIdeal i))
              (Units.map (baseChangeLocalizationHom A' p.1).toMonoidHom
                (P.factorUnit q.asIdeal j))
              (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)) := by
  rw [TameSymbolPreparation.symbolValue, map_prod]
  conv_lhs => rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun q _ => ?_
  exact map_norm_factorizationValue_pow_eq_prod_support (A := A) (A' := A')
    (B := Localization.AtPrime q.asIdeal) (π := P.parameter q.asIdeal)
    (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal)) hm
    (P.factorUnit q.asIdeal i) (P.factorUnit q.asIdeal j)
    (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)

end General

end Support

end Stacks.Chow

end
