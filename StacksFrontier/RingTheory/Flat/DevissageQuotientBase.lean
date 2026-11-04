module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport
public import StacksFrontier.RingTheory.Flat.DevissageLocalize
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange

/-!
# Base change of a complete dévissage along a ring map of the base

Stacks 05PG proves its flattening statement by induction along a complete dévissage, and its
induction step is the sentence *"thus we may replace `A` by `A/J`"*: having produced an ideal
`J ⊆ A` corepresenting a subfunctor, one passes from the base `A` to the base `A/J`, carrying the
complete dévissage along. The library transports a dévissage along a localization of the base
(`Module.CompleteDevissage.localize`) and along an isomorphism of the base
(`Module.CompleteDevissage.ofRingEquiv`), and this file begins the transport along a general ring
map of the base, which is what that step needs.

## The conditions, one by one

Write `R → R'` for the map of the base, `r` for the prime of `R` the dévissage is over and `r'`
for a prime of `R'` lying over `r`; for a surjection `R → R/J` with `J ⊆ r`, take `r' = r/J`. A
stage of a dévissage is base changed by replacing `S`, `N`, `Aᵢ`, `Bᵢ`, `Mᵢ` by `S ⊗_R R'`,
`N ⊗_R R'`, … and every map by its base change. Of the conditions of Stacks 05HX and 05HZ:

*Formal under any ring map.* `initial_surjective`, `transition_surjective` and `final_surjective`
are right exactness of the tensor product; `finiteM` and `left_finite` are stability of module
finiteness under base change; `initial_finitePresentation` and `transition_finitePresentation` are
stability of finite presentation (the universe mismatch between `S` and `A₀` is handled as in
`Stacks.Flatness.finitePresentation_mapₐ_of_isLocalization`, by the kernel of a surjection);
`smooth` and `geometricallyIrreducibleFibers` are stability of smoothness and of geometrically
irreducible fibres under base change; `initialEquiv` and `cokerEquiv` are again right exactness.

*`map_isPrime` and `fiber_bijective`.* These need the prime `r'`.

That `r'B'ᵢ` is *prime* is, as in Stacks 05HX itself, a consequence of the smoothness and fibre
hypotheses and not an extra condition — but it is not formal. For a general ring map,
`B'ᵢ/r'B'ᵢ = (R'/r') ⊗_{R/r} (Bᵢ/rBᵢ)` injects into
`κ(r') ⊗_{κ(r)} (κ(r) ⊗_R Bᵢ)` because `Bᵢ` is flat over `R`, and the fibre `κ(r) ⊗_R Bᵢ` is
geometrically integral — irreducible by hypothesis and reduced because `Bᵢ` is smooth — so it
stays a domain over the field extension `κ(r')/κ(r)`. The same flatness gives the contraction
`rBᵢ = (r'B'ᵢ) ∩ Bᵢ`, hence the extension of residue fields `κ(rBᵢ) → κ(r'B'ᵢ)`, along which
`α'ᵢ ⊗ κ(r'B'ᵢ)` is `(αᵢ ⊗ κ(rBᵢ)) ⊗ κ(r'B'ᵢ)` and so bijective.

For a *surjection* `R → R/J` with `J ⊆ r` all of this collapses: `B'ᵢ = Bᵢ/JBᵢ` and
`r'B'ᵢ = rBᵢ/JBᵢ`, so `B'ᵢ/r'B'ᵢ = Bᵢ/rBᵢ`, the fibre prime is prime for the old reason, the two
residue fields agree, and the fibre condition is the old condition. That is what
`Stacks.Flatness.isPrime_map_algebraMap_of_surjective`,
`Stacks.Flatness.map_algebraMap_eq_comap_of_surjective`,
`Stacks.Flatness.bijective_residueFieldMap_of_surjective` and
`Stacks.Flatness.fiber_bijective_of_isBaseChange` below prove.

*The two prime-and-support conditions of Stacks 05HZ.* `residueField_purelyTranscendental` and
`lowerPrime_mem_fiberSupport` are about the chosen primes, and they are the reason the pointed
dévissage transports along a **surjection** and not along a general ring map.

* For a surjection `R → R/J` with `J ⊆ r` the primes transport canonically and the conditions are
  unchanged. The primes of `Bᵢ/JBᵢ` are the primes of `Bᵢ` containing `JBᵢ`, and every prime over
  `r` contains `rBᵢ ⊇ JBᵢ`, so `qᵢ` *is* a prime of the new stage; its residue field is unchanged,
  as is the residue field `κ(r) = κ(r/J)` of the base, so
  `residueField_purelyTranscendental` is the same statement, transported along the two canonical
  isomorphisms of residue fields by `PurelyTranscendental.of_ringEquiv` below. The fibre ring is
  unchanged, `κ(r/J) ⊗_{R/J} Bᵢ/JBᵢ = κ(r) ⊗_R Bᵢ`, hence so are the fibre module and
  `lowerPrime_mem_fiberSupport`.
* For a general ring map there is no transport, and the source claims none. The prime of `B'ᵢ` is
  not free to choose: `initial_under` forces `upperPrime 0` to contract to `q'`, hence forces
  `lowerPrime 0`, and the hypotheses of 05HZ say nothing about the residue extension of the forced
  prime over `κ(r')` nor about the local dimension of the support at it. (Nothing here shows the
  pointed notion *fails* to transport along an arbitrary ring map; it shows there is no formal
  transport. Stacks 05PG needs only the surjective case, where the forced prime is the old one.)

*`relativeDimension_eq_support`.* This one is subtler than it looks, because the two sides move
differently: the right-hand side is a dimension of a fibre, which base change is transparent to,
while the left-hand side `dim(Bᵢ/R)` is a *supremum over all primes of `Bᵢ`* and the base change
of `Bᵢ` has fewer primes — for a surjection, only those containing `JBᵢ`. So the supremum can
only drop, and the condition would be broken by any drop.

It does not drop, and the reason is
`Module.NonemptyCompleteDevissageAt.relativeDimensionAt_lowerPrime_eq` below: in a pointed
dévissage the supremum `dim(Bᵢ/R)` is *attained at the stage prime* `qᵢ`. Indeed the support of the
fibre module is a subspace of the fibre of `Spec Bᵢ → Spec R` over `r`, so the right-hand side of
the condition is at most `dim_{qᵢ}(Bᵢ/R)`, which is at most the supremum, which *is* the right-hand
side. Since relative dimension at a prime is invariant under base change (Stacks 00QI,
`Algebra.IsPushout.relativeDimensionAt_comap_eq`), the new supremum is again attained, at any prime
of `B'ᵢ` over `qᵢ`, and the condition survives — for an arbitrary ring map of the base, not only a
surjection. That is `Module.NonemptyCompleteDevissageAt.relativeDimension_eq_of_isPushout`.

## Main results

The fibre prime and the fibre condition under a surjection of the base, the counterparts for a
surjection of the localization lemmas of `StacksFrontier.RingTheory.Flat.DevissageBaseChange`:

* `Stacks.Flatness.isPrime_map_algebraMap_of_surjective` and
  `Stacks.Flatness.map_algebraMap_eq_comap_of_surjective`: the ideal `r'B'` is prime and contracts
  to `rB`, as soon as the kernel of `B → B'` lands inside `rB`.
* `Stacks.Flatness.bijective_residueFieldMap_of_surjective`: the residue field is then unchanged,
  `κ(rB) ≅ κ(r'B')`.
* `Stacks.Flatness.isBaseChange_finsuppMapRange`: a finite free module base changes to a finite
  free module, which is what `Stacks.Flatness.bijective_baseChange_of_isLocalization` got from
  `IsLocalizedModule.isBaseChange` and a general base change has to be told.
* `Stacks.Flatness.bijective_baseChange_alpha_of_isBaseChange` and
  `Stacks.Flatness.fiber_bijective_of_isBaseChange`: the fibre condition on `α` survives, in the
  shape the structure field asks for.

The pure-transcendence condition:

* `PurelyTranscendental.of_ringEquiv`: pure transcendence transported along isomorphisms of the
  base field *and* of the extension, which is what replacing `κ(r)` and `κ(qᵢ)` by the residue
  fields of the quotient needs.

The dimension condition:

* `topologicalKrullDimAt_subtype_le`: the dimension of a subspace at a point is at most the
  dimension of the ambient space there.
* `Algebra.relativeDimensionAt_le_relativeDimension` and
  `Algebra.relativeDimension_le_of_isPushout`: `dim_𝔮(S/R) ≤ dim(S/R)`, and a base change can only
  decrease `dim(S/R)`.
* `Algebra.relativeDimensionAt_eq_topologicalKrullDimAt_fiber`: the relative dimension at a prime,
  read in the fibre ring rather than in the set-theoretic fibre.
* `Algebra.topologicalKrullDimAt_support_fiber_le_relativeDimensionAt`: the local dimension of the
  support of a fibre module at a point of the fibre is at most the relative dimension there.
* `Module.NonemptyCompleteDevissageAt.relativeDimensionAt_lowerPrime_eq`: in a pointed complete
  dévissage the relative dimension of a stage algebra is attained at that stage's prime.
* `Module.NonemptyCompleteDevissageAt.relativeDimension_eq_of_isPushout`: hence the dimension
  condition of Stacks 05HZ survives an arbitrary base change of the base ring.

## What is not here

The assembly of these into a `Module.CompleteDevissage (R/J) S' N' (r/J)` and a
`Module.NonemptyCompleteDevissageAt (R/J) S' N' q'`, and the one remaining condition it needs:
the identification `κ(r/J) ⊗_{R/J} (Bᵢ/JBᵢ) ≅ κ(r) ⊗_R Bᵢ` of fibre rings, along which
`lowerPrime_mem_fiberSupport` moves by `Module.support_eq_comap_preimage` and
`mem_support_fiber_iff` of
`StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport` — those two carry the support
condition across an isomorphism of the fibre *ring*, so what is owed is the isomorphism, whose
proof is the `Algebra.IsPushout.comp_iff` computation of
`StacksFrontier.RingTheory.RelativeDimension.BaseChange`.

As for `Module.CompleteDevissage.localize`, the assembly cannot take the stage algebras and stage
modules as abstract types: the dependent fields `alpha`, `cokerEquiv` and `fiber_bijective` are
typed against the module structure restricted along the base-changed `toLeft`, so the stage data
has to be *defined*, as `Aᵢ ⧸ JAᵢ`, `Bᵢ ⧸ JBᵢ` and `Mᵢ ⧸ (JAᵢ • ⊤)`.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 00QI](https://stacks.math.columbia.edu/tag/00QI)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u v w

/-! ### The fibre prime of a stage under a surjection of the base -/

namespace Stacks.Flatness

/-- **The fibre prime of a stage stays prime after a surjective base change**, provided the kernel
of the surjection of the stage algebras lands inside it. For the base change along `R → R/J` with
`J ⊆ r` that kernel is `JBᵢ ⊆ rBᵢ`.

This is the surjective counterpart of
`Stacks.Flatness.isPrime_map_algebraMap_of_disjoint`; both go through
`Stacks.Flatness.map_map_algebraMap_eq`, the identification of the new fibre ideal `r'B'` with the
image of the old one `rB`. -/
public theorem isPrime_map_algebraMap_of_surjective {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (r : Ideal R) (R' : Type*) [CommRing R'] [Algebra R R']
    (B' : Type*) [CommRing B'] [Algebra R B'] [Algebra B B'] [Algebra R' B']
    [IsScalarTower R B B'] [IsScalarTower R R' B']
    [(Ideal.map (algebraMap R B) r).IsPrime]
    (hs : Function.Surjective (algebraMap B B'))
    (hker : RingHom.ker (algebraMap B B') ≤ Ideal.map (algebraMap R B) r) :
    (Ideal.map (algebraMap R' B') (Ideal.map (algebraMap R R') r)).IsPrime := by
  rw [map_map_algebraMap_eq B r R' B']
  exact Ideal.map_isPrime_of_surjective hs hker

/-- **The fibre prime of the base-changed stage contracts to the old fibre prime** along a
surjection whose kernel lands inside the old fibre prime. This is the hypothesis under which the
two residue fields agree. -/
public theorem map_algebraMap_eq_comap_of_surjective {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (r : Ideal R) (R' : Type*) [CommRing R'] [Algebra R R']
    (B' : Type*) [CommRing B'] [Algebra R B'] [Algebra B B'] [Algebra R' B']
    [IsScalarTower R B B'] [IsScalarTower R R' B']
    (hs : Function.Surjective (algebraMap B B'))
    (hker : RingHom.ker (algebraMap B B') ≤ Ideal.map (algebraMap R B) r) :
    Ideal.map (algebraMap R B) r =
      (Ideal.map (algebraMap R' B') (Ideal.map (algebraMap R R') r)).comap (algebraMap B B') := by
  rw [map_map_algebraMap_eq B r R' B', Ideal.comap_map_of_surjective _ hs,
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]

/-- **A prime survives a surjection with the same residue field, as soon as it is the contraction
of its image.** This is the identification `κ(rB) ≅ κ(r'B')` that the fibre condition of a
base-changed dévissage stage is transported along when the base change is a surjection; the
counterpart for a localization is
`Stacks.Flatness.bijective_residueFieldMap_of_isLocalization`. The content is that a surjection
is surjective on stalks. -/
public theorem bijective_residueFieldMap_of_surjective {B B' : Type*} [CommRing B] [CommRing B']
    [Algebra B B'] (hs : Function.Surjective (algebraMap B B'))
    (p : Ideal B) [p.IsPrime] (p' : Ideal B') [p'.IsPrime]
    (hp' : p = p'.comap (algebraMap B B')) :
    Function.Bijective (Ideal.ResidueField.map p p' (algebraMap B B') hp') :=
  (RingHom.surjectiveOnStalks_of_surjective hs).residueFieldMap_bijective p p' hp'

/-! ### The fibre condition on `α` under a base change -/

/-- **A finite free module base changes to a finite free module**, in the form the fibre condition
of a dévissage stage needs: `B'^(⊕ι)` is the base change of `B^(⊕ι)` along `B → B'`, the map being
`Finsupp.mapRange` of the structure map. This is `IsBaseChange.of_basis` for the standard basis of
a finsupp module, and is what replaces `IsLocalizedModule.isBaseChange` of
`Stacks.Flatness.bijective_baseChange_of_isLocalization` when the base change is not a
localization. -/
public theorem isBaseChange_finsuppMapRange (B : Type*) [CommRing B] (B' : Type*) [CommRing B']
    [Algebra B B'] (ι : Type*) :
    IsBaseChange B' (Finsupp.mapRange.linearMap (α := ι) (Algebra.linearMap B B')) := by
  classical
  have heq : (Finsupp.linearCombination B (Finsupp.basisSingleOne (R := B') (ι := ι)) :
        (ι →₀ B) →ₗ[B] (ι →₀ B'))
      = Finsupp.mapRange.linearMap (Algebra.linearMap B B') := by
    refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
    simp [Finsupp.linearCombination_single, Algebra.algebraMap_eq_smul_one]
  rw [← heq]
  exact IsBaseChange.of_basis B Finsupp.basisSingleOne

/-- **The fibre condition on the map of a dévissage stage survives a base change**, stated with
the fibre field of the base change still abstract.

This is `Stacks.Flatness.bijective_baseChange_of_isLocalization` with the localization hypotheses
on the module replaced by a base change, and it is applied in exactly the same way: the fibre
field `L` is a variable rather than `κ(r'B')` because its algebra structures over `B` and over `K`
have to be constructed, and constructing them inside the proof puts the tensor products
`L ⊗[B'] _` out of reach of instance synthesis.
`Stacks.Flatness.fiber_bijective_of_isBaseChange` constructs them and applies this lemma as a
term. -/
public theorem bijective_baseChange_alpha_of_isBaseChange {B : Type*} [CommRing B] {M : Type*}
    [AddCommGroup M] [Module B M] {m : ℕ} (alpha : (Fin m →₀ B) →ₗ[B] M)
    {B' : Type*} [CommRing B'] [Algebra B B']
    {M' : Type*} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {g : M →ₗ[B] M'} (hg : IsBaseChange B' g)
    (alpha' : (Fin m →₀ B') →ₗ[B'] M')
    (halpha : ∀ x, alpha' (Finsupp.mapRange.linearMap (Algebra.linearMap B B') x) = g (alpha x))
    {K : Type*} [CommRing K] [Algebra B K]
    {L : Type*} [CommRing L] [Algebra B L] [Algebra B' L] [IsScalarTower B B' L]
    [Algebra K L] [IsScalarTower B K L]
    (hKL : Function.Bijective (algebraMap K L))
    (hf : Function.Bijective (alpha.baseChange K)) :
    Function.Bijective (alpha'.baseChange L) := by
  refine bijective_baseChange_of_isBaseChange alpha hKL
    ((isBaseChange_finsuppMapRange B B' (Fin m)).comp
      (TensorProduct.isBaseChange B' (Fin m →₀ B') L))
    (hg.comp (TensorProduct.isBaseChange B' M' L))
    (alpha'.baseChange L) (fun x => ?_) hf
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    TensorProduct.mk_apply, LinearMap.baseChange_tmul, halpha]

/-- **The fibre condition on the map of a dévissage stage survives a base change**, in the shape
the `fiber_bijective` field of the base-changed stage asks for.

The hypotheses are: `M'` is the base change of `M` along `B → B'` (`hg`), `alpha'` is the base
change of `alpha` (`halpha`), the new fibre prime `p'` contracts to the old one `p` (`hp'`), and
the induced map of residue fields is bijective (`hres`). For a surjective base change `hres` is
`Stacks.Flatness.bijective_residueFieldMap_of_surjective` and `hp'` is
`Stacks.Flatness.map_algebraMap_eq_comap_of_surjective`; for a localization they are the two
lemmas of `StacksFrontier.RingTheory.Flat.DevissageBaseChange`, and this is
`Stacks.Flatness.fiber_bijective_of_isLocalization` with the localization hypotheses on the module
weakened to a base change.

A general base change of the base ring does *not* make `hres` bijective — it makes
`κ(rB) → κ(r'B')` a field extension — but bijectivity is more than the conclusion needs: the base
change of a bijective map of modules over a field along any extension of that field is bijective.
Supplying that in place of `hres` would give the fibre condition for an arbitrary base change. -/
public theorem fiber_bijective_of_isBaseChange {B : Type*} [CommRing B] {M : Type*}
    [AddCommGroup M] [Module B M] {m : ℕ} (alpha : (Fin m →₀ B) →ₗ[B] M)
    {B' : Type*} [CommRing B'] [Algebra B B']
    {M' : Type*} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {g : M →ₗ[B] M'} (hg : IsBaseChange B' g)
    (alpha' : (Fin m →₀ B') →ₗ[B'] M')
    (halpha : ∀ x, alpha' (Finsupp.mapRange.linearMap (Algebra.linearMap B B') x) = g (alpha x))
    (p : Ideal B) [p.IsPrime] (p' : Ideal B') [p'.IsPrime]
    (hp' : p = p'.comap (algebraMap B B'))
    (hres : Function.Bijective (Ideal.ResidueField.map p p' (algebraMap B B') hp'))
    (hf : Function.Bijective (alpha.baseChange p.ResidueField)) :
    Function.Bijective (alpha'.baseChange p'.ResidueField) :=
  let _ : Algebra B p'.ResidueField :=
    ((algebraMap B' p'.ResidueField).comp (algebraMap B B')).toAlgebra
  have _ : IsScalarTower B B' p'.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra p.ResidueField p'.ResidueField :=
    (Ideal.ResidueField.map p p' (algebraMap B B') hp').toAlgebra
  have _ : IsScalarTower B p.ResidueField p'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (Ideal.ResidueField.map_algebraMap p p' (algebraMap B B') hp' b).symm
  bijective_baseChange_alpha_of_isBaseChange alpha hg alpha' halpha hres hf

end Stacks.Flatness

/-! ### Pure transcendence under isomorphisms of both fields -/

/-- **Pure transcendence transported along isomorphisms of the base field and of the extension.**

`PurelyTranscendental.of_ringEquiv_base` changes the model of the base field and
`AlgEquiv.purelyTranscendental` changes the model of the extension over a fixed base; this
combines the two. It is what the pure-transcendence condition of Stacks 05HZ needs under a
*surjective* base change of the base ring: there both the residue field `κ(r)` of the base prime
and the residue field `κ(qᵢ)` of the stage prime are replaced by isomorphic models — for
`R → R/J` with `J ⊆ r` they are replaced by themselves, up to the canonical isomorphisms
`R/r ≅ (R/J)/(r/J)` and `Bᵢ/qᵢ ≅ (Bᵢ/JBᵢ)/(qᵢ/JBᵢ)`. -/
public theorem PurelyTranscendental.of_ringEquiv {K K' L L' : Type*} [Field K] [Field K']
    [Field L] [Field L'] [Algebra K L] [Algebra K' L'] (psi : K ≃+* K') (phi : L ≃+* L')
    (h : ∀ x : K, phi (algebraMap K L x) = algebraMap K' L' (psi x))
    [PurelyTranscendental K L] : PurelyTranscendental K' L' :=
  let : Algebra K L' := ((algebraMap K' L').comp psi.toRingHom).toAlgebra
  have hKL' : ∀ x : K, algebraMap K L' x = algebraMap K' L' (psi x) := fun _ => rfl
  have _ : PurelyTranscendental K L' :=
    (AlgEquiv.ofRingEquiv (f := phi) fun x => (h x).trans (hKL' x).symm).purelyTranscendental
  PurelyTranscendental.of_ringEquiv_base psi fun x => (hKL' x).symm

/-! ### The dimension of a subspace at a point -/

/-- **The dimension of a subspace at a point is at most the dimension of the ambient space at that
point.** Every open neighbourhood `U` of the point in `X` cuts out the open neighbourhood
`val ⁻¹' U` of it in `s`, whose dimension is that of `U ∩ s` and so at most that of `U`. -/
public theorem topologicalKrullDimAt_subtype_le {X : Type*} [TopologicalSpace X] (s : Set X)
    (x : s) : topologicalKrullDimAt ↥s x ≤ topologicalKrullDimAt X ↑x := by
  simp only [topologicalKrullDimAt]
  refine le_iInf fun U => iInf_le_of_le
    ⟨Subtype.val ⁻¹' U.1, U.2.1, U.2.2.preimage continuous_subtype_val⟩ ?_
  show topologicalKrullDim ↥((Subtype.val : s → X) ⁻¹' U.1) ≤ topologicalKrullDim ↥U.1
  rw [← Subtype.preimage_coe_inter_self s U.1,
    topologicalKrullDim_preimage_val s (U.1 ∩ s) Set.inter_subset_right]
  exact topologicalKrullDim_le_of_subset Set.inter_subset_left

/-! ### Relative dimension at a prime versus relative dimension -/

namespace Algebra

/-- **The relative dimension at a prime is at most the relative dimension**, the latter being the
supremum of the former over all primes. -/
public theorem relativeDimensionAt_le_relativeDimension (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    Algebra.relativeDimensionAt R 𝔮 ≤ Algebra.relativeDimension R S :=
  le_iSup (fun 𝔭 : PrimeSpectrum S => Algebra.relativeDimensionAt R 𝔭.asIdeal) ⟨𝔮, ‹_›⟩

/-- **A base change can only decrease the relative dimension.** Every prime of `S'` has the same
relative dimension as the prime of `S` below it (Stacks 00QI), so the supremum over the primes of
`S'` is a supremum over a subfamily of the one over the primes of `S`. -/
public theorem relativeDimension_le_of_isPushout (R S R' S' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R S R' S']
    [Algebra.FiniteType R S] :
    Algebra.relativeDimension R' S' ≤ Algebra.relativeDimension R S := by
  refine iSup_le fun 𝔮' => ?_
  rw [← Algebra.IsPushout.relativeDimensionAt_comap_eq R S R' S' 𝔮']
  exact relativeDimensionAt_le_relativeDimension R _

/-- **A base change leaves the relative dimension unchanged as soon as the supremum defining it is
attained at a prime that survives the base change.** -/
public theorem relativeDimension_eq_of_isPushout (R S R' S' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R S R' S']
    [Algebra.FiniteType R S] (𝔮' : Ideal S') [𝔮'.IsPrime] {𝔮 : Ideal S} [𝔮.IsPrime]
    (h𝔮 : 𝔮'.comap (algebraMap S S') = 𝔮)
    (h : Algebra.relativeDimensionAt R 𝔮 = Algebra.relativeDimension R S) :
    Algebra.relativeDimension R' S' = Algebra.relativeDimension R S := by
  subst h𝔮
  refine le_antisymm (relativeDimension_le_of_isPushout R S R' S') ?_
  rw [← h]
  exact (Algebra.IsPushout.relativeDimensionAt_comap_eq R S R' S' ⟨𝔮', ‹_›⟩).trans_le
    (relativeDimensionAt_le_relativeDimension R' 𝔮')

/-! ### Relative dimension in the fibre ring -/

/-- **The relative dimension at a prime, read in the fibre ring.** `Algebra.relativeDimensionAt`
is the dimension of the subspace `comap (algebraMap R B) ⁻¹' {p}` of `Spec B` at `lp`;
`PrimeSpectrum.preimageHomeomorphFiber` identifies that subspace with `Spec (κ(p) ⊗_R B)` and
carries `lp` to the point `PrimeSpectrum.primesOverOrderIsoFiber R B p lp` of the fibre ring. -/
public theorem relativeDimensionAt_eq_topologicalKrullDimAt_fiber (R : Type*) {B : Type*}
    [CommRing R] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (lp : Ideal B) [lp.IsPrime]
    (hlp : lp ∈ p.primesOver B) :
    Algebra.relativeDimensionAt R lp
      = topologicalKrullDimAt (PrimeSpectrum (p.Fiber B))
          (PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩) := by
  have hcomap : PrimeSpectrum.comap (algebraMap R B) (⟨lp, ‹_›⟩ : PrimeSpectrum B)
      = (⟨p, ‹_›⟩ : PrimeSpectrum R) := PrimeSpectrum.ext hlp.2.over.symm
  have hset : PrimeSpectrum.comap (algebraMap R B) ⁻¹'
        {PrimeSpectrum.comap (algebraMap R B) (⟨lp, ‹_›⟩ : PrimeSpectrum B)}
      = PrimeSpectrum.comap (algebraMap R B) ⁻¹' {(⟨p, ‹_›⟩ : PrimeSpectrum R)} := by
    rw [hcomap]
  rw [Algebra.relativeDimensionAt,
    topologicalKrullDimAt_congr_set hset _ rfl (Set.mem_preimage.mpr hcomap),
    topologicalKrullDimAt_eq_of_homeomorph (PrimeSpectrum.preimageHomeomorphFiber R B ⟨p, ‹_›⟩)]
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The local dimension of the support of a fibre module is at most the relative dimension at
the point.** The support is a subspace of `Spec (κ(p) ⊗_R B)`, whose dimension at the point of the
fibre cut out by `lp` is `Algebra.relativeDimensionAt R lp`. -/
public theorem topologicalKrullDimAt_support_fiber_le_relativeDimensionAt (R : Type*) {B : Type*}
    [CommRing R] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (lp : Ideal B) [lp.IsPrime]
    (hlp : lp ∈ p.primesOver B) (M : Type*) [AddCommGroup M] [Module B M]
    (hmem : PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩ ∈
      Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) M)) :
    topologicalKrullDimAt ↥(Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) M))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩, hmem⟩
      ≤ Algebra.relativeDimensionAt R lp := by
  rw [relativeDimensionAt_eq_topologicalKrullDimAt_fiber R p lp hlp]
  exact topologicalKrullDimAt_subtype_le _ _

end Algebra

/-! ### The dimension condition of a pointed complete dévissage -/

namespace Module.NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S}
  [q.IsPrime]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **In a pointed complete dévissage the relative dimension of a stage algebra is attained at
that stage's prime.**

The dimension condition of Stacks 05HZ says that `dim(Bᵢ/R)` is the local dimension of the support
of the fibre module at the point `qᵢ` of the fibre. That support is a subspace of the whole fibre,
so the condition bounds `dim(Bᵢ/R)` above by `dim_{qᵢ}(Bᵢ/R)`, which is one of the terms of the
supremum `dim(Bᵢ/R)`. Hence the two are equal.

This is what makes the dimension condition survive a base change of the base ring: the supremum is
pinned to a prime, and the relative dimension at a prime is a base change invariant. -/
public theorem relativeDimensionAt_lowerPrime_eq (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    Algebra.relativeDimensionAt R (D.lowerPrime i)
      = Algebra.relativeDimension R (D.toCompleteDevissage.B i) := by
  refine le_antisymm (Algebra.relativeDimensionAt_le_relativeDimension R _) ?_
  rw [D.relativeDimension_eq_support i]
  exact Algebra.topologicalKrullDimAt_support_fiber_le_relativeDimensionAt R (q.under R)
    (D.lowerPrime i) ⟨D.lowerPrime_isPrime i, D.lowerPrime_liesOver i⟩
    (D.toCompleteDevissage.M i) (D.lowerPrime_mem_fiberSupport i)

/-- **The dimension condition of a pointed complete dévissage survives an arbitrary base change of
the base ring.**

Let `B'` be the base change of the stage algebra `Bᵢ` along any ring map `R → R'` and let `lp'` be
a prime of `B'` contracting to the stage prime `qᵢ`. Then `dim(B'/R') = dim(Bᵢ/R)`: the supremum
`dim(Bᵢ/R)` is attained at `qᵢ` by
`Module.NonemptyCompleteDevissageAt.relativeDimensionAt_lowerPrime_eq`, and relative dimension at a
prime is invariant under base change (Stacks 00QI).

Since the fibre module of the base-changed stage is the old one for a surjection `R → R/J` with
`J ⊆ r`, this is the transport of `relativeDimension_eq_support` for that case; the hypothesis on
`lp'` is then automatic, `qᵢ` itself being a prime of `Bᵢ/JBᵢ`. -/
public theorem relativeDimension_eq_of_isPushout (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) (R' : Type*) (B' : Type*) [CommRing R']
    [CommRing B'] [Algebra R R'] [Algebra R' B'] [Algebra (D.toCompleteDevissage.B i) B']
    [Algebra R B'] [IsScalarTower R R' B']
    [IsScalarTower R (D.toCompleteDevissage.B i) B']
    [Algebra.IsPushout R (D.toCompleteDevissage.B i) R' B'] (lp' : Ideal B') [lp'.IsPrime]
    (hlp' : lp'.comap (algebraMap (D.toCompleteDevissage.B i) B') = D.lowerPrime i) :
    Algebra.relativeDimension R' B'
      = Algebra.relativeDimension R (D.toCompleteDevissage.B i) :=
  Algebra.relativeDimension_eq_of_isPushout R (D.toCompleteDevissage.B i) R' B' lp' hlp'
    (D.relativeDimensionAt_lowerPrime_eq i)

end Module.NonemptyCompleteDevissageAt

end
