module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeFibre

/-!
# Stacks 0EPG as a single product over the maximal ideals of the flat base change

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian local
rings, let `m = length_{A'}(A' / 𝔪A')` and let `A ⊆ B` be a finite extension carrying a
tame-symbol preparation. The source spells the right-hand side of Stacks 0EPG as

`∂_{A'}(a₁, a₂) = ∏_{j, l} Norm_{κ'_{j,l}/κ'}(w_j mod 𝔪'_{j,l})^{m'_{j,l}}`,

where `𝔪'_{j,l}` runs over the maximal ideals of `B' = A' ⊗_A B` lying over the maximal ideal
`𝔪_j` of `B`, where `B'_{j,l}` is the localization of `B'` at `𝔪'_{j,l}`, and where the
factorization data at `𝔪'_{j,l}` is the image of the data at `𝔪_j` under `B_j → B'_{j,l}`. The
pairs `(j, l)` exhaust the maximal ideals of `B'`, so this is one product over
`MaximalSpectrum (A' ⊗_A B)` with each factor read in the local ring `(A' ⊗_A B)_𝔭`.

`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeFibre` produces the identity
with the factor at a pair `(𝔮, p)` read in `(A' ⊗_A B_𝔮)_p` instead, and identifies the two index
sets. This file carries the factors across that identification and assembles the single product.

The transport is the observation that the two local rings coincide: `A' ⊗_A B_𝔮` is a localization
of `A' ⊗_A B` at the image of the complement of `𝔮`, so localizing it at `p` localizes
`A' ⊗_A B` at `p ∩ (A' ⊗_A B) = 𝔭`. The resulting isomorphism is one of `A'`-algebras and is
compatible with the two maps out of `B_𝔮`, and both ingredients of a factor — the order of
vanishing of the parameter and the norm to `κ'` of the residue of the unit — are unchanged by an
isomorphism of local rings over `A'`.

## Main definitions

* `Stacks.Chow.baseChangeLocalRingHom` — the map `B_𝔮 → (A' ⊗_A B)_𝔭` for a maximal ideal `𝔭` of
  the base change lying over `𝔮`.
* `Stacks.Chow.baseChangeFibreHom` — that map at the maximal ideal of `B` below `𝔭`.

## Main results

* `Stacks.Chow.units_map_norm_factorizationValue_algEquiv` — the residue-field norm of the factor
  of Stacks 0EAQ is unchanged by an isomorphism of local rings over a common local base.
* `Stacks.Chow.exists_baseChangeFibreLocalizationAlgEquiv` — `(A' ⊗_A B_𝔮)_p` and
  `(A' ⊗_A B)_𝔭` are the same `A'`-algebra, compatibly with the structure maps from
  `A' ⊗_A B`.
* `Stacks.Chow.units_map_norm_factorizationValue_baseChange` — the factor of Stacks 0EPG is the
  same at the two models of the local ring.
* `Stacks.Chow.map_symbolValue_pow_eq_prod_maximalSpectrum` — Stacks 0EPG with the right-hand side
  as one product over `MaximalSpectrum (A' ⊗_A B)`, each factor read in `(A' ⊗_A B)_𝔭`.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0GU1](https://stacks.math.columbia.edu/tag/0GU1)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section InstanceTransport

variable {R : Type*} [CommRing R] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- **Locality of the structure map is carried along an isomorphism of algebras.** -/
theorem isLocalHom_algebraMap_of_algEquiv (e : S ≃ₐ[R] T) [h : IsLocalHom (algebraMap R S)] :
    IsLocalHom (algebraMap R T) where
  map_nonunit x hx := by
    have h1 : IsUnit (e (algebraMap R S x)) := by rwa [e.commutes]
    have h2 : IsUnit (e.symm (e (algebraMap R S x))) := h1.map (e.symm : T →* S)
    rw [e.symm_apply_apply] at h2
    exact h.map_nonunit x h2

/-- **Finiteness of the residue-field extension is carried along an isomorphism of algebras.** -/
theorem moduleFinite_residueField_of_algEquiv (e : S ≃ₐ[R] T) [IsLocalRing R] [IsLocalRing S]
    [IsLocalRing T] [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [Module.Finite (ResidueField R) (ResidueField S)] :
    Module.Finite (ResidueField R) (ResidueField T) :=
  Module.Finite.equiv (ResidueField.mapAlgEquiv' e).toLinearEquiv

/-- A localization at a prime is a localization at any prime equal to it. -/
theorem isLocalization_atPrime_of_eq (W : Type*) [CommRing W] [Algebra R W] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) [IsLocalization.AtPrime W I] :
    IsLocalization.AtPrime W J := by
  subst h
  infer_instance

end InstanceTransport

section FiniteLocalAlgebra

variable {R : Type*} [CommRing R] [IsLocalRing R] {S : Type*} [CommRing S] [Algebra R S]
  [Module.Finite R S]

/-- **A finite algebra over a local ring is local at every one of its maximal ideals.** A maximal
ideal `𝔭` of a finite — hence integral — `R`-algebra `S` contracts to a maximal ideal of `R`, so
to `𝔪_R`; every nonunit of `R` therefore lands in `𝔭` and so in the maximal ideal of `S_𝔭`. This
is `Stacks.Chow.isLocalHom_algebraMap_localizationAtPrime` as an instance at a point of the
maximal spectrum. -/
instance isLocalHom_algebraMap_localizationAtPrime_maximalSpectrum (𝔭 : MaximalSpectrum S) :
    IsLocalHom (algebraMap R (Localization.AtPrime 𝔭.asIdeal)) :=
  isLocalHom_algebraMap_localizationAtPrime 𝔭.asIdeal

/-- **The residue field at a maximal ideal of a finite algebra over a local ring is finite over
the base residue field.** The residue field at `𝔭` is a finite `R`-module, because `S` is one and
it is a quotient of `S_𝔭`, and the `R`-module structure factors through `κ_R`. -/
instance moduleFinite_residueField_localizationAtPrime (𝔭 : MaximalSpectrum S) :
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime 𝔭.asIdeal)) := by
  have : Module.Finite R (ResidueField (Localization.AtPrime 𝔭.asIdeal)) :=
    Module.Finite.trans S _
  exact Module.Finite.of_restrictScalars_finite R _ _

end FiniteLocalAlgebra

section FactorTransport

variable {R : Type*} [CommRing R] [IsLocalRing R] {S T : Type*} [CommRing S] [CommRing T]
  [IsLocalRing S] [IsLocalRing T] [Algebra R S] [Algebra R T] [IsLocalHom (algebraMap R S)]
  [IsLocalHom (algebraMap R T)]

/-- **The factor of Stacks 0EAQ is carried along an isomorphism of local rings.** The order of
vanishing of the parameter is unchanged, and the residue of the unit is carried by the induced
isomorphism of residue fields. -/
theorem units_map_factorizationValue_mapAlgEquiv (e : S ≃ₐ[R] T) (π : S) (u v : Sˣ) (n k : ℕ) :
    factorizationValue (e π) (Units.map (e : S →* T) u) (Units.map (e : S →* T) v) n k =
      Units.map (ResidueField.mapAlgEquiv' e : ResidueField S →* ResidueField T)
        (factorizationValue π u v n k) := by
  have hord : (Ring.ord T (e π)).toNat = (Ring.ord S π).toNat :=
    ord_toNat_of_ringEquiv e.toRingEquiv π
  have hres (x : Sˣ) : Units.map (residue T).toMonoidHom (Units.map (e : S →* T) x) =
      Units.map (ResidueField.mapAlgEquiv' e : ResidueField S →* ResidueField T)
        (Units.map (residue S).toMonoidHom x) :=
    Units.ext (by simp [ResidueField.mapAlgEquiv'_residue])
  have hneg : Units.map (ResidueField.mapAlgEquiv' e : ResidueField S →* ResidueField T)
      (-1 : (ResidueField S)ˣ) = (-1 : (ResidueField T)ˣ) := Units.ext (by simp)
  rw [factorizationValue, factorizationValue, hord, ← map_pow]
  simp only [map_mul, map_pow, map_inv, hres, hneg]

/-- **The residue-field norm of the factor of Stacks 0EAQ is unchanged by an isomorphism of local
rings over a common local base.** This is what makes the factor of Stacks 0EPG independent of the
model chosen for the local ring at a maximal ideal of the base change. -/
theorem units_map_norm_factorizationValue_algEquiv (e : S ≃ₐ[R] T) (π : S) (u v : Sˣ) (n k : ℕ) :
    Units.map (Algebra.norm (ResidueField R) : ResidueField T →* ResidueField R)
        (factorizationValue (e π) (Units.map (e : S →* T) u) (Units.map (e : S →* T) v) n k) =
      Units.map (Algebra.norm (ResidueField R) : ResidueField S →* ResidueField R)
        (factorizationValue π u v n k) := by
  rw [units_map_factorizationValue_mapAlgEquiv, units_map_norm_residueField_mapAlgEquiv]

/-- **The factor of Stacks 0EAQ at a unit parameter is trivial.** The quotient by a unit vanishes,
so the order of vanishing is zero. -/
theorem factorizationValue_eq_one_of_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : IsUnit π) (u v : Rˣ) (n k : ℕ) : factorizationValue π u v n k = 1 := by
  simp [factorizationValue, Ring.ord_of_isUnit hπ]

end FactorTransport

section FibreHom

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')]
  {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **The map `B_𝔮 → (A' ⊗_A B)_𝔭`.** For a maximal ideal `𝔭` of the base change lying over the
maximal ideal `𝔮` of `B` the elements of `B` outside `𝔮` become invertible at `𝔭`, so the
structure map `B → (A' ⊗_A B)_𝔭` factors through `B_𝔮`. This is the map along which the local
factorization data of `B_𝔮` is carried to `(A' ⊗_A B)_𝔭` in the proof of Stacks 0EPG. -/
noncomputable def baseChangeLocalRingHom (q : MaximalSpectrum B)
    (𝔭 : MaximalSpectrum (A' ⊗[A] B)) (hq : 𝔭.asIdeal.under B = q.asIdeal) :
    Localization.AtPrime q.asIdeal →+* Localization.AtPrime 𝔭.asIdeal :=
  Localization.localRingHom q.asIdeal 𝔭.asIdeal (algebraMap B (A' ⊗[A] B)) hq.symm

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- The map `baseChangeLocalRingHom` sends the image of `b : B` in `B_𝔮` to the image in
`(A' ⊗_A B)_𝔭` of `1 ⊗ b`. -/
@[simp]
theorem baseChangeLocalRingHom_algebraMap (q : MaximalSpectrum B)
    (𝔭 : MaximalSpectrum (A' ⊗[A] B)) (hq : 𝔭.asIdeal.under B = q.asIdeal) (b : B) :
    baseChangeLocalRingHom q 𝔭 hq (algebraMap B (Localization.AtPrime q.asIdeal) b) =
      algebraMap (A' ⊗[A] B) (Localization.AtPrime 𝔭.asIdeal)
        (algebraMap B (A' ⊗[A] B) b) :=
  Localization.localRingHom_to_map _ _ _ _ b

/-- **The map `B_𝔮 → (A' ⊗_A B)_𝔭` at the maximal ideal `𝔮` of `B` below `𝔭`.** This is the map
the source uses to transport the factorization data of `B_𝔮` to `B'_{j,l}`. -/
noncomputable def baseChangeFibreHom (𝔭 : MaximalSpectrum (A' ⊗[A] B)) :
    Localization.AtPrime (baseChangeUnder 𝔭).asIdeal →+* Localization.AtPrime 𝔭.asIdeal :=
  baseChangeLocalRingHom (baseChangeUnder 𝔭) 𝔭 rfl

/-- **The factor of Stacks 0EPG at `𝔭` does not depend on how the maximal ideal below `𝔭` is
presented.** Reading the preparation data at a maximal ideal `𝔮` of `B` that `𝔭` lies over gives
the same factor as reading it at `𝔭 ∩ B`. -/
theorem units_map_norm_factorizationValue_baseChangeFibreHom
    (𝔭 : MaximalSpectrum (A' ⊗[A] B)) (q : MaximalSpectrum B) (hq : baseChangeUnder 𝔭 = q)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r) :
    Units.map (Algebra.norm (ResidueField A') :
        ResidueField (Localization.AtPrime 𝔭.asIdeal) →* ResidueField A')
        (factorizationValue (baseChangeFibreHom 𝔭 (P.parameter (baseChangeUnder 𝔭).asIdeal))
          (Units.map (baseChangeFibreHom 𝔭).toMonoidHom
            (P.factorUnit (baseChangeUnder 𝔭).asIdeal i))
          (Units.map (baseChangeFibreHom 𝔭).toMonoidHom
            (P.factorUnit (baseChangeUnder 𝔭).asIdeal j))
          (P.exponent (baseChangeUnder 𝔭).asIdeal i)
          (P.exponent (baseChangeUnder 𝔭).asIdeal j)) =
      Units.map (Algebra.norm (ResidueField A') :
        ResidueField (Localization.AtPrime 𝔭.asIdeal) →* ResidueField A')
        (factorizationValue
          (baseChangeLocalRingHom q 𝔭 (congrArg MaximalSpectrum.asIdeal hq)
            (P.parameter q.asIdeal))
          (Units.map (baseChangeLocalRingHom q 𝔭 (congrArg MaximalSpectrum.asIdeal hq)).toMonoidHom
            (P.factorUnit q.asIdeal i))
          (Units.map (baseChangeLocalRingHom q 𝔭 (congrArg MaximalSpectrum.asIdeal hq)).toMonoidHom
            (P.factorUnit q.asIdeal j))
          (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)) := by
  subst hq
  rfl

/-- **A unit parameter at a maximal ideal `𝔮` of `B` is a unit parameter at `𝔭 ∩ B`** whenever
`𝔭` lies over `𝔮`. -/
theorem isUnit_parameter_baseChangeUnder (𝔭 : MaximalSpectrum (A' ⊗[A] B))
    (q : MaximalSpectrum B) (hq : baseChangeUnder 𝔭 = q)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B)
    (hu : IsUnit (P.parameter q.asIdeal)) :
    IsUnit (P.parameter (baseChangeUnder 𝔭).asIdeal) := by
  subst hq
  exact hu

end FibreHom

section SingleFactor

variable (A : Type u) [CommRing A] [IsLocalRing A] (A' : Type v) [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')]
  {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B]

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Finite A B] in
/-- **The two models of the local ring at a maximal ideal of the base change agree.** Let `𝔮` be a
maximal ideal of `B`, let `p` be a maximal ideal of `A' ⊗_A B_𝔮` and let `𝔭` be its contraction to
`A' ⊗_A B`. Then `(A' ⊗_A B)_𝔭` and `(A' ⊗_A B_𝔮)_p` are isomorphic as `A'`-algebras, compatibly
with the structure maps from `A' ⊗_A B`.

The input is `Stacks.Chow.isLocalization_baseChangeSemilocalization`, that `A' ⊗_A B_𝔮` is the
localization of `A' ⊗_A B` at the image of the complement of `𝔮`, together with
`Stacks.Localization.isLocalization_atPrime_under`, that localizing such a semilocalization at a
prime localizes the base at the prime below it. -/
theorem exists_baseChangeFibreLocalizationAlgEquiv (q : MaximalSpectrum B)
    (𝔭 : MaximalSpectrum (A' ⊗[A] B))
    (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))
    (h𝔭 : 𝔭.asIdeal = Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal) :
    ∃ e : Localization.AtPrime 𝔭.asIdeal ≃ₐ[A'] Localization.AtPrime p.asIdeal,
      ∀ z : A' ⊗[A] B,
        e (algebraMap (A' ⊗[A] B) (Localization.AtPrime 𝔭.asIdeal) z) =
          algebraMap (A' ⊗[A] Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal)
            (baseChangeSemilocalization A A' q z) := by
  let := baseChangeSemilocalizationAlgebra A A' q
  have := isScalarTower_baseChangeSemilocalization A A' q
  have := isLocalization_baseChangeSemilocalization A A' q
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.under (A' ⊗[A] B)) :=
    isLocalization_atPrime_under (R := B) (T := A' ⊗[A] B) (p := q.asIdeal)
      (Q := p.asIdeal) (W := Localization.AtPrime p.asIdeal)
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) 𝔭.asIdeal :=
    isLocalization_atPrime_of_eq _ h𝔭.symm
  have : IsScalarTower A' (A' ⊗[A] B) (Localization.AtPrime p.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap A' (Localization.AtPrime p.asIdeal) x =
        algebraMap (A' ⊗[A] Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal)
          (algebraMap (A' ⊗[A] B) (A' ⊗[A] Localization.AtPrime q.asIdeal)
            (algebraMap A' (A' ⊗[A] B) x))
      rw [← IsScalarTower.algebraMap_apply A' (A' ⊗[A] B)
          (A' ⊗[A] Localization.AtPrime q.asIdeal),
        ← IsScalarTower.algebraMap_apply A' (A' ⊗[A] Localization.AtPrime q.asIdeal)
          (Localization.AtPrime p.asIdeal)]
  set e₀ := IsLocalization.algEquiv 𝔭.asIdeal.primeCompl
    (Localization.AtPrime 𝔭.asIdeal) (Localization.AtPrime p.asIdeal) with he₀
  refine ⟨AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun x => ?_), fun z => ?_⟩
  · rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) (Localization.AtPrime 𝔭.asIdeal)]
    show e₀ (algebraMap (A' ⊗[A] B) (Localization.AtPrime 𝔭.asIdeal)
      (algebraMap A' (A' ⊗[A] B) x)) = _
    rw [e₀.commutes, IsScalarTower.algebraMap_apply A' (A' ⊗[A] B)
      (Localization.AtPrime p.asIdeal)]
  · show e₀ (algebraMap (A' ⊗[A] B) (Localization.AtPrime 𝔭.asIdeal) z) = _
    rw [e₀.commutes]
    rfl

omit [IsLocalRing A] [IsLocalHom (algebraMap A A')] in
/-- **The factor of Stacks 0EPG at the two models of the local ring at `𝔭`.** Let `𝔮` be a maximal
ideal of `B`, let `𝔭` be a maximal ideal of `A' ⊗_A B` lying over `𝔮`, and let `p` be a maximal
ideal of `A' ⊗_A B_𝔮` contracting to `𝔭`. Reading the factor of Stacks 0EAQ in `(A' ⊗_A B_𝔮)_p`,
as `Stacks.Chow.map_norm_factorizationValue_pow_eq_prod_support` does, gives the same unit of `κ'`
as reading it in `(A' ⊗_A B)_𝔭`, as the source does.

The two local rings are identified by
`Stacks.Chow.exists_baseChangeFibreLocalizationAlgEquiv`, that identification carries `B_𝔮 → `
one model to `B_𝔮 → ` the other, and the factor survives an isomorphism of local rings over `A'`
by `Stacks.Chow.units_map_norm_factorizationValue_algEquiv`. -/
theorem units_map_norm_factorizationValue_baseChange
    (q : MaximalSpectrum B) (𝔭 : MaximalSpectrum (A' ⊗[A] B))
    (hq : 𝔭.asIdeal.under B = q.asIdeal)
    (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))
    (h𝔭 : 𝔭.asIdeal = Ideal.comap (baseChangeSemilocalization A A' q).toRingHom p.asIdeal)
    [IsLocalHom (algebraMap A' (Localization.AtPrime p.asIdeal))]
    (π : Localization.AtPrime q.asIdeal) (u v : (Localization.AtPrime q.asIdeal)ˣ) (n k : ℕ) :
    Units.map (Algebra.norm (ResidueField A') :
        ResidueField (Localization.AtPrime p.asIdeal) →* ResidueField A')
        (factorizationValue (baseChangeLocalizationHom A' p π)
          (Units.map (baseChangeLocalizationHom A' p).toMonoidHom u)
          (Units.map (baseChangeLocalizationHom A' p).toMonoidHom v) n k) =
      Units.map (Algebra.norm (ResidueField A') :
        ResidueField (Localization.AtPrime 𝔭.asIdeal) →* ResidueField A')
        (factorizationValue (baseChangeLocalRingHom q 𝔭 hq π)
          (Units.map (baseChangeLocalRingHom q 𝔭 hq).toMonoidHom u)
          (Units.map (baseChangeLocalRingHom q 𝔭 hq).toMonoidHom v) n k) := by
  obtain ⟨e, he⟩ := exists_baseChangeFibreLocalizationAlgEquiv A A' q 𝔭 p h𝔭
  have hcomp (x : Localization.AtPrime q.asIdeal) :
      baseChangeLocalizationHom A' p x = e (baseChangeLocalRingHom q 𝔭 hq x) := by
    have hring := IsLocalization.ringHom_ext (S := Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl
      (j := baseChangeLocalizationHom A' p)
      (k := (e : Localization.AtPrime 𝔭.asIdeal →+* Localization.AtPrime p.asIdeal).comp
        (baseChangeLocalRingHom q 𝔭 hq)) ?_
    · exact DFunLike.congr_fun hring x
    · ext b
      show baseChangeLocalizationHom A' p (algebraMap B (Localization.AtPrime q.asIdeal) b) =
        e (baseChangeLocalRingHom q 𝔭 hq (algebraMap B (Localization.AtPrime q.asIdeal) b))
      rw [baseChangeLocalRingHom_algebraMap, he, algebraMap_right_eq_includeRight,
        baseChangeSemilocalization_includeRight, baseChangeLocalizationHom_apply]
  have hu (x : (Localization.AtPrime q.asIdeal)ˣ) :
      Units.map (baseChangeLocalizationHom A' p).toMonoidHom x =
        Units.map (e : Localization.AtPrime 𝔭.asIdeal →* Localization.AtPrime p.asIdeal)
          (Units.map (baseChangeLocalRingHom q 𝔭 hq).toMonoidHom x) :=
    Units.ext (hcomp x)
  rw [hcomp π, hu u, hu v, units_map_norm_factorizationValue_algEquiv]

end SingleFactor

section General

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A']
  [IsLocalHom (algebraMap A A')] [Module.Flat A A']
  {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum (A' ⊗[A] B))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]

/-- **Stacks 0EPG for a general pair of nonzerodivisors, as a single product over the maximal
ideals of the base change.** Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of
one-dimensional Noetherian local rings and let `m = length_{A'}(A' / 𝔪A')`. Let `A ⊆ B` be a
finite extension carrying a tame-symbol preparation of a family `a` of elements of `A` — by
Stacks 0EAG one exists for *every* pair of nonzerodivisors of `A`. Then the value of the formula
Stacks 0EAQ for two members of that family, raised to the power `m` and read in `κ'`, is

`(∏_𝔮 Norm_{κ(𝔮)/κ}(w_𝔮)^{m_𝔮})^m = ∏_𝔭 Norm_{κ(𝔭)/κ'}(w_{𝔭 ∩ B})^{m_𝔭}`,

the product on the right running over *all* the maximal ideals `𝔭` of `A' ⊗_A B` and the factor at
`𝔭` being computed in the local ring `(A' ⊗_A B)_𝔭`, from the image of the factorization data at
`𝔮 = 𝔭 ∩ B` under `B_𝔮 → (A' ⊗_A B)_𝔭`. This is the spelling of the source: there the maximal
ideals of `B' = A' ⊗_A B` are listed as `𝔪'_{j,l}`, the maximal ideals above `𝔪_j`, the factor at
`𝔪'_{j,l}` is read in `B'_{j,l}`, and "as factorizations of `a₁` and `a₂` in `B'_{j,l}` we use the
image of the factorizations `a_i = u_{i,j} π_j^{e_{i,j}}` given to us in `B_j`".

`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` is the same identity with the right-hand
side presented fibre by fibre over the maximal ideals of `B` and the factor in each fibre read in
`(A' ⊗_A B_𝔮)_p` rather than in `(A' ⊗_A B)_𝔭`; the two index sets are identified by
`Stacks.Chow.baseChangeSupportSigmaEquiv` and the two factors agree by
`Stacks.Chow.units_map_norm_factorizationValue_baseChange`.

The identification of the index sets holds fibre by fibre at a maximal ideal `𝔮` of `B` whose
parameter lies in the maximal ideal of `B_𝔮`. At a maximal ideal whose parameter is a unit no
identification is needed: the support of the parameter in `A' ⊗_A B_𝔮` is then empty, and over
`𝔮` the order of vanishing in `(A' ⊗_A B)_𝔭` is zero, so both fibre products are `1`. -/
@[stacks 0EPG "for a general pair of nonzerodivisors, in the spelling of the source: the formula \
Stacks 0EAQ over `A` for a tame-symbol preparation on a finite extension `B` of `A`, which \
Stacks 0EAG provides for every pair, raised to the power `m` and read in `κ'`, is one product \
over the maximal ideals `𝔭` of `A' ⊗_A B`, the factor at `𝔭` being the norm to `κ'` of the \
formula Stacks 0EAQ computed in `(A' ⊗_A B)_𝔭` for the image of the factorization data at \
`𝔭 ∩ B`"]
theorem map_symbolValue_pow_eq_prod_maximalSpectrum
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    [∀ q : MaximalSpectrum B,
      Fintype (Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal))] :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom (P.symbolValue i j) ^ m =
      ∏ 𝔭 : MaximalSpectrum (A' ⊗[A] B),
        Units.map (Algebra.norm (ResidueField A') :
            ResidueField (Localization.AtPrime 𝔭.asIdeal) →* ResidueField A')
          (factorizationValue (baseChangeFibreHom 𝔭 (P.parameter (baseChangeUnder 𝔭).asIdeal))
            (Units.map (baseChangeFibreHom 𝔭).toMonoidHom
              (P.factorUnit (baseChangeUnder 𝔭).asIdeal i))
            (Units.map (baseChangeFibreHom 𝔭).toMonoidHom
              (P.factorUnit (baseChangeUnder 𝔭).asIdeal j))
            (P.exponent (baseChangeUnder 𝔭).asIdeal i)
            (P.exponent (baseChangeUnder 𝔭).asIdeal j)) := by
  have hfin : Module.length A' (A' ⧸ extendedMaximalIdeal A A') ≠ ⊤ := by
    rw [hm]; exact ENat.natCast_ne_top m
  have hart : ∀ q : MaximalSpectrum B,
      IsArtinianRing (Localization.AtPrime q.asIdeal ⧸ Ideal.span {P.parameter q.asIdeal}) :=
    fun q => isArtinianRing_quotient_span
      (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal))
  have hfib : ∀ q : MaximalSpectrum B,
      Fintype {𝔭 : MaximalSpectrum (A' ⊗[A] B) // baseChangeUnder 𝔭 = q} :=
    fun _ => Fintype.ofFinite _
  -- at a maximal ideal of `B` whose parameter is a unit the support is empty and every factor
  -- over that maximal ideal is trivial, so the two presentations agree there as well
  have hempty : ∀ q : MaximalSpectrum B,
      P.parameter q.asIdeal ∉ maximalIdeal (Localization.AtPrime q.asIdeal) →
        IsEmpty (Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal)) := by
    intro q hq
    refine ⟨fun p => p.1.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ p.2 ?_)⟩
    exact (IsLocalRing.notMem_maximalIdeal.mp hq).map
      (Algebra.TensorProduct.includeRight (R := A) (A := A')
        (B := Localization.AtPrime q.asIdeal))
  have hlocres : ∀ (q : MaximalSpectrum B)
      (p : Stacks.Length.tensorSupport A A' (P.parameter q.asIdeal)),
      ∃ _ : IsLocalHom (algebraMap A' (Localization.AtPrime p.1.asIdeal)),
        Module.Finite (ResidueField A') (ResidueField (Localization.AtPrime p.1.asIdeal)) := by
    intro q p
    by_cases hmem : P.parameter q.asIdeal ∈ maximalIdeal (Localization.AtPrime q.asIdeal)
    · obtain ⟨e, -⟩ := exists_baseChangeFibreLocalizationAlgEquiv A A' q
        (baseChangeFibreEquiv A A' q hfin (hart q) hmem p).1 p.1 rfl
      have := isLocalHom_algebraMap_of_algEquiv e
      exact ⟨this, moduleFinite_residueField_of_algEquiv e⟩
    · exact ((hempty q hmem).false p).elim
  have hloc := fun q p => (hlocres q p).fst
  have hres := fun q p => (hlocres q p).snd
  rw [map_symbolValue_pow_eq_prod_prod_support hm P i j,
    prod_maximalSpectrum_baseChange_eq_prod_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  by_cases hmem : P.parameter q.asIdeal ∈ maximalIdeal (Localization.AtPrime q.asIdeal)
  · refine Fintype.prod_equiv (baseChangeFibreEquiv A A' q hfin (hart q) hmem) _ _ fun p => ?_
    exact (units_map_norm_factorizationValue_baseChange A A' q
        (baseChangeFibreEquiv A A' q hfin (hart q) hmem p).1
        (congrArg MaximalSpectrum.asIdeal (baseChangeFibreEquiv A A' q hfin (hart q) hmem p).2)
        p.1 rfl _ _ _ _ _).trans
      (units_map_norm_factorizationValue_baseChangeFibreHom _ q
        (baseChangeFibreEquiv A A' q hfin (hart q) hmem p).2 P i j).symm
  · have := hempty q hmem
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    refine (Finset.prod_eq_one fun 𝔭 _ => ?_).symm
    rw [factorizationValue_eq_one_of_isUnit
      ((isUnit_parameter_baseChangeUnder 𝔭.1 q 𝔭.2 P
        (IsLocalRing.notMem_maximalIdeal.mp hmem)).map (baseChangeFibreHom 𝔭.1)), map_one]

end General

end Stacks.Chow

end
