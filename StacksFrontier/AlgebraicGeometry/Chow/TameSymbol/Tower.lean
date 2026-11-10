module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFibreTransport

/-!
# Tame symbols along a tower of finite modifications

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring, let `A ⊆ B` be a finite ring extension
with `𝔪` not an associated prime of `B`, and let `B ⊆ C` be a further finite extension. Stacks
0EAT asserts

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product being over the maximal ideals of `B`.

The source's `∂` is the recipe of Stacks 0EAQ — "we do not claim there is a unique map with these
properties" — and a recipe takes an extension of the ring it is applied to as an argument. Both
sides of the displayed equation are therefore read here relative to a common refinement `C`: the
left-hand side is the norm pushforward `Stacks.Chow.normProd` of a family of tame symbols on the
local rings of `C` to `A`, and the factor at `𝔮` is the norm pushforward of the same family to
`B_𝔮` along the semilocalization `C_𝔮`, whose maximal ideals are the maximal ideals of `C` over
`𝔮` and whose local rings are the local rings of `C` there. Each side is a genuine tame symbol in
the sense of Stacks 0EAH, by `Stacks.Chow.normPushforward`.

The equation is then the source's proof: the maximal ideals of `C` are the `𝔪_{𝔮, v}` lying over
the maximal ideals `𝔮` of `B`, and transitivity of norms for `κ(𝔪_{𝔮, v})/κ(𝔮)/κ(𝔪)` (Stacks
0BIJ) regroups the product over the maximal ideals of `C` into the iterated product. The
correspondence of maximal ideals is *derived*, from `Stacks.Localization.maximalSpectrumSigmaEquiv`
and `Stacks.Localization.localizationAtPrimeUnderAlgEquiv`, rather than assumed.

The spelling of Stacks 0EAT in which no refinement appears on the right-hand side is
`Stacks.Chow.normProd_eq_prod_norm_tameSymbol`, in
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Refinement`, which imports this file: there the
factor at `𝔮` is an arbitrary tame symbol on `B_𝔮` itself, at the cost of a tame-symbol
preparation of the two elements over `B` as a hypothesis. The independence of the recipe from the
refinement that makes that possible — Stacks 0EAR beyond the fixed-extension case
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_sameExtension` — is
`Stacks.Chow.normProd_eq_preparationSymbolValue` in the same file.

## Main definitions

* `Stacks.Chow.symmNonZeroDivisor` — a nonzerodivisor pulled back along a ring isomorphism.
* `Stacks.Chow.RegularTameSymbol.transport` — a tame symbol carried along an isomorphism of local
  rings over a common base.
* `Stacks.Chow.fibrePoint` — the maximal ideal of `C` below a maximal ideal of `C_𝔮`.
* `Stacks.Chow.fibreSymbol` — the family of tame symbols on the local rings of the
  semilocalization `C_𝔮` induced by a family on the local rings of `C`.

## Main results

* `Stacks.Chow.mem_nonZeroDivisors_ringEquiv` — nonzerodivisors are carried along a ring
  isomorphism.
* `Stacks.Chow.isScalarTower_localizationAtPrime_under` — `A → B_𝔮 → C_𝔯` is a tower.
* `Stacks.Chow.units_map_norm_fibreSymbol` — the factor of Stacks 0EAT at a maximal ideal of `C`.
* `Stacks.Chow.normProd_eq_prod_norm_normProd` — Stacks 0EAT for the norm pushforward.
* `Stacks.Chow.normPushforward_apply_eq_prod_norm_normPushforward` — the same equation between
  the two tame symbols the two sides define.

## Implementation notes

`Stacks.Chow.fibrePoint` is reducible, so that the local ring at it is syntactically the local
ring of `C` at the contracted prime and the algebra structures over `B_𝔮` supplied as instance
hypotheses apply to it.

## References

* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0BIJ](https://stacks.math.columbia.edu/tag/0BIJ)
-/

@[expose] public section

open IsLocalRing Stacks.Localization

universe u v w

namespace Stacks.Chow

/-! ### Carrying a tame symbol along an isomorphism of local rings -/

section NonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Nonzerodivisors are carried along a ring isomorphism.** -/
theorem mem_nonZeroDivisors_ringEquiv (e : R ≃+* S) {x : R} (hx : x ∈ nonZeroDivisors R) :
    e x ∈ nonZeroDivisors S := by
  rw [← MulEquivClass.map_nonZeroDivisors e]
  exact Submonoid.mem_map_of_mem e hx

/-- A nonzerodivisor of `S` as a nonzerodivisor of `R`, along an isomorphism `R ≃+* S`. -/
def symmNonZeroDivisor (e : R ≃+* S) (x : nonZeroDivisors S) : nonZeroDivisors R :=
  ⟨e.symm x, mem_nonZeroDivisors_ringEquiv e.symm x.2⟩

/-- The underlying element of a pulled-back nonzerodivisor is the image under the inverse. -/
@[simp]
theorem symmNonZeroDivisor_val (e : R ≃+* S) (x : nonZeroDivisors S) :
    (symmNonZeroDivisor e x : R) = e.symm (x : S) := rfl

/-- Pulling back nonzerodivisors along a ring isomorphism is multiplicative. -/
theorem symmNonZeroDivisor_mul (e : R ≃+* S) (x y : nonZeroDivisors S) :
    symmNonZeroDivisor e (x * y) = symmNonZeroDivisor e x * symmNonZeroDivisor e y :=
  Subtype.ext (map_mul e.symm (x : S) (y : S))

end NonZeroDivisors

namespace RegularTameSymbol

section Transport

variable {T : Type*} [CommRing T] [IsLocalRing T] {R S : Type*} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra T R] [Algebra T S] [IsLocalHom (algebraMap T R)]
  [IsLocalHom (algebraMap T S)]

/-- **A tame symbol carried along an isomorphism of local rings over a common base.** The symbol
of the target is read off the symbol of the source by pulling back the two arguments and pushing
the resulting unit of the residue field forward. -/
noncomputable def transport (symb : RegularTameSymbol R) (e : R ≃ₐ[T] S) :
    RegularTameSymbol S where
  toFun x y :=
    Units.map (ResidueField.mapAlgEquiv' e : ResidueField R →* ResidueField S)
      (symb (symmNonZeroDivisor e.toRingEquiv x) (symmNonZeroDivisor e.toRingEquiv y))
  map_mul_left a a' b := by
    rw [symmNonZeroDivisor_mul, symb.map_mul_left, map_mul]
  map_mul_right a b b' := by
    rw [symmNonZeroDivisor_mul, symb.map_mul_right, map_mul]
  self b := by
    have hord : (Ring.ord R (symmNonZeroDivisor e.toRingEquiv b : R)).toNat =
        (Ring.ord S (b : S)).toNat := by
      rw [← ord_of_ringEquiv e.toRingEquiv (symmNonZeroDivisor e.toRingEquiv b : R)]
      simp only [symmNonZeroDivisor_val, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.coe_mk, EquivLike.coe_coe,
        AlgEquiv.apply_symm_apply]
    rw [symb.self, hord, map_pow]
    exact congrArg (· ^ (Ring.ord S (b : S)).toNat)
      (Units.ext (by simp only [Units.map_neg, map_one, Units.val_neg, Units.val_one]))
  unit_left a b u hu := by
    have hu' : (symmNonZeroDivisor e.toRingEquiv a : R) =
        (Units.map (e.symm : S →* R) u : Rˣ) := by
      simp only [symmNonZeroDivisor_val, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, hu, RingEquiv.coe_mk, EquivLike.coe_coe, Units.coe_map,
        MonoidHom.coe_ofClass]
    have hord : (Ring.ord R (symmNonZeroDivisor e.toRingEquiv b : R)).toNat =
        (Ring.ord S (b : S)).toNat := by
      rw [← ord_of_ringEquiv e.toRingEquiv (symmNonZeroDivisor e.toRingEquiv b : R)]
      simp only [symmNonZeroDivisor_val, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.coe_mk, EquivLike.coe_coe,
        AlgEquiv.apply_symm_apply]
    rw [symb.unit_left _ _ (Units.map (e.symm : S →* R) u) hu', hord, map_pow]
    exact congrArg (· ^ (Ring.ord S (b : S)).toNat)
      (Units.ext (by simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map,
        MonoidHom.coe_ofClass, ResidueField.mapAlgEquiv'_residue, AlgEquiv.apply_symm_apply]))
  steinberg a b c hc := by
    have hc' : (symmNonZeroDivisor e.toRingEquiv c : R) =
        (symmNonZeroDivisor e.toRingEquiv b : R) - (symmNonZeroDivisor e.toRingEquiv a : R) := by
      simp only [symmNonZeroDivisor_val, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, hc, RingEquiv.coe_mk, EquivLike.coe_coe, map_sub]
    rw [← map_mul, ← map_mul, symb.steinberg _ _ _ hc']

/-- The value of a transported tame symbol: the value of the original symbol on the pulled-back
arguments, pushed forward to the residue field of the target. -/
@[simp]
theorem transport_apply (symb : RegularTameSymbol R) (e : R ≃ₐ[T] S) (x y : nonZeroDivisors S) :
    symb.transport e x y =
      Units.map (ResidueField.mapAlgEquiv' e : ResidueField R →* ResidueField S)
        (symb (symmNonZeroDivisor e.toRingEquiv x) (symmNonZeroDivisor e.toRingEquiv y)) :=
  rfl

end Transport

end RegularTameSymbol

/-! ### Stacks 0EAT along a tower -/

section Tower

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] {C : Type w} [CommRing C] [Algebra B C]
  [Module.Finite B C] [Algebra A C] [IsScalarTower A B C]

omit [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A] in
/-- **The local rings along a fibre form a tower.** For a maximal ideal `𝔮` of `B` and a maximal
ideal `v` of the semilocalization of `C` at `𝔮`, the structure maps make `C` localized at the
prime below `v` an algebra over `B_𝔮` compatibly with its algebra structure over `A`. -/
theorem isScalarTower_localizationAtPrime_under (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    [Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    [IsScalarTower B (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (v.asIdeal.under C))] :
    IsScalarTower A (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (v.asIdeal.under C)) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal),
    IsScalarTower.algebraMap_apply A C (Localization.AtPrime (v.asIdeal.under C)),
    IsScalarTower.algebraMap_apply A B C,
    Localization.AtPrime.algebraMap_eq]
  exact (Localization.localRingHom_to_map q.asIdeal (v.asIdeal.under C) (algebraMap B C) _
    (algebraMap A B x)).symm

variable [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ (q : MaximalSpectrum B)
      (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
  [∀ (q : MaximalSpectrum B)
      (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]

/-- **The maximal ideal of `C` below a maximal ideal of the semilocalization of `C` at `𝔮`.** -/
abbrev fibrePoint (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :
    MaximalSpectrum C :=
  ⟨Ideal.under C v.asIdeal, (maximalSpectrumSigmaEquiv B C ⟨q, v⟩).isMaximal⟩

/-- **The family of tame symbols on the local rings of the semilocalization `C_𝔮`** induced by a
family on the local rings of `C`: the local ring of `C_𝔮` at a maximal ideal `v` is the local ring
of `C` at the prime below `v`, and the symbol there is carried along that isomorphism. -/
noncomputable def fibreSymbol
    (symb : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :
    RegularTameSymbol (Localization.AtPrime v.asIdeal) :=
  (symb (fibrePoint q v)).transport (fibreLocalizationAlgEquiv q v)

/-- **The factor of Stacks 0EAT at a maximal ideal of `C`.** The residue-field norm down to `κ(𝔪)`
of the symbol at a maximal ideal `𝔯` of `C` over `𝔮` is the norm down to `κ(𝔪)` of the norm down
to `κ(𝔮)` of the symbol there, by transitivity of norms for `κ(𝔯)/κ(𝔮)/κ(𝔪)`. -/
theorem units_map_norm_fibreSymbol
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (symb : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (q : MaximalSpectrum B)
    (hfib : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (a b : nonZeroDivisors A) :
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime (fibrePoint q v).asIdeal) →* ResidueField A)
      (symb (fibrePoint q v) (toExtensionNonZeroDivisor hC (fibrePoint q v) a)
        (toExtensionNonZeroDivisor hC (fibrePoint q v) b)) =
      Units.map (Algebra.norm (ResidueField A) :
          ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
        (Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
            ResidueField (Localization.AtPrime v.asIdeal) →*
              ResidueField (Localization.AtPrime q.asIdeal))
          (fibreSymbol symb q v
            (toExtensionNonZeroDivisor hfib v (toExtensionNonZeroDivisor hB q a))
            (toExtensionNonZeroDivisor hfib v (toExtensionNonZeroDivisor hB q b)))) := by
  have htower := isScalarTower_localizationAtPrime_under (A := A) q v
  have harg : ∀ x : nonZeroDivisors A,
      symmNonZeroDivisor (fibreLocalizationAlgEquiv q v).toRingEquiv
          (toExtensionNonZeroDivisor hfib v (toExtensionNonZeroDivisor hB q x)) =
        toExtensionNonZeroDivisor hC (fibrePoint q v) x := by
    intro x
    have key : (fibreLocalizationAlgEquiv q v)
          (algebraMap A (Localization.AtPrime (Ideal.under C v.asIdeal)) (x : A)) =
        algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime v.asIdeal)
          (algebraMap A (Localization.AtPrime q.asIdeal) (x : A)) := by
      rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (Ideal.under C v.asIdeal))]
      exact fibreLocalizationAlgEquiv_algebraMap q v _
    refine Subtype.ext ?_
    rw [symmNonZeroDivisor_val, toExtensionNonZeroDivisor_val, toExtensionNonZeroDivisor_val,
      toExtensionNonZeroDivisor_val, ← key]
    exact (fibreLocalizationAlgEquiv q v).symm_apply_apply _
  rw [fibreSymbol, RegularTameSymbol.transport_apply, harg, harg,
    units_map_norm_residueField_mapAlgEquiv (fibreLocalizationAlgEquiv q v)]
  exact (units_map_norm_residueField_comp (A := A) (B := Localization.AtPrime q.asIdeal) _).symm

variable [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B,
    Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]

/-- **Stacks 0EAT.** Let `(A, 𝔪)` be a one-dimensional Noetherian local ring, let `A ⊆ B` be a
finite ring extension with `𝔪` not an associated prime of `B`, and let `B ⊆ C` be a further finite
extension with `𝔪` not an associated prime of `C`. Then

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product being over the maximal ideals `𝔮` of `B`, where `∂_A` is the norm pushforward to `A`
of a family of tame symbols on the local rings of `C` and `∂_{B_𝔮}` is the norm pushforward of
the same family to `B_𝔮` along the semilocalization `C_𝔮`.

This is the source's proof: the maximal ideals of `C` are the maximal ideals of the
semilocalizations `C_𝔮`, whose local rings are the local rings of `C`, and transitivity of norms
for `κ(𝔪_{𝔮, v})/κ(𝔮)/κ(𝔪)` (Stacks 0BIJ) turns the product over the maximal ideals of `C` into
the iterated product. -/
@[stacks 0EAT "the displayed equation, for both symbols read as the recipe of Stacks 0EAQ relative
to the common refinement C the statement quantifies over; the non-associated-prime hypothesis of
the source is imposed at each stage of the tower, and the correspondence between the maximal
ideals of C and those of B is derived here from the semilocalizations rather than assumed.
The spelling in which no refinement appears on the right-hand side is
Stacks.Chow.normProd_eq_prod_norm_tameSymbol"]
theorem normProd_eq_prod_norm_normProd
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (symb : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (a b : nonZeroDivisors A) :
    normProd hC symb a b =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (normProd (hfibre q) (fibreSymbol symb q)
            (toExtensionNonZeroDivisor hB q a) (toExtensionNonZeroDivisor hB q b)) := by
  rw [normProd_eq, prod_maximalSpectrum_eq_prod_prod B C]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [normProd_eq, map_prod]
  exact Finset.prod_congr rfl fun v _ =>
    units_map_norm_fibreSymbol hB hC symb q (hfibre q) v a b

/-- **Stacks 0EAT between the two tame symbols the two sides define.** Both the norm pushforward
to `A` and each norm pushforward to `B_𝔮` are tame symbols in the sense of Stacks 0EAH, by
`Stacks.Chow.normPushforward`, and the displayed equation of Stacks 0EAT relates them. -/
@[stacks 0EAT "the displayed equation between the two tame symbols of Stacks 0EAH that the two
sides define, for the recipe of Stacks 0EAQ relative to the common refinement C the statement
quantifies over"]
theorem normPushforward_apply_eq_prod_norm_normPushforward [Module.Finite A C]
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (symb : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (hinj : Function.Injective (algebraMap A C))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C))
    (hinjFibre : ∀ q : MaximalSpectrum B,
      Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquotFibre : ∀ q : MaximalSpectrum B,
      ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (a b : nonZeroDivisors A) :
    normPushforward hC symb hinj hquot a b =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (normPushforward (hfibre q) (fibreSymbol symb q) (hinjFibre q) (hquotFibre q)
            (toExtensionNonZeroDivisor hB q a) (toExtensionNonZeroDivisor hB q b)) :=
  normProd_eq_prod_norm_normProd hB hC hfibre symb a b

end Tower

end Stacks.Chow

end
