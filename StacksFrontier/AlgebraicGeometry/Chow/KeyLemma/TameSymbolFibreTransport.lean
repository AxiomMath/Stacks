module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFactorizationIndependence
public import StacksFrontier.RingTheory.Localization.SemilocalizationFibre

/-!
# Transport of the tame-symbol data along the fibres of a finite extension

Let `A ⊆ B ⊆ C` be finite extensions of a one-dimensional Noetherian local ring. Comparing the
tame-symbol formula (0EAQ) over `B` with the formula over `C` requires two passages, both carried
out here.

The first is a *transport of preparations*: a tame-symbol preparation of a family over `B` gives a
preparation of the same family over `C`, whose parameter at a maximal ideal `𝔯` of `C` is the image
of the parameter at the maximal ideal `𝔮 = 𝔯 ∩ B`, and whose units and exponents are likewise the
images and the same numbers. The one fact this cannot supply is that the image of a nonzerodivisor
of `B_𝔮` is a nonzerodivisor of `C_𝔯`, which is carried as a hypothesis.

The second is a *transport along the fibre*. The maximal ideals of `C` over `𝔮` are the maximal
ideals of the semilocalization `C_𝔮`, and the local ring of `C_𝔮` at such a maximal ideal `v` is
the local ring of `C` at the prime of `C` below `v`. That identification is an isomorphism of
`C`-algebras; here it is upgraded to an isomorphism of `B_𝔮`-algebras, and the order of vanishing
and the residue-field norm are shown to be unchanged by it. Transporting

`λ ^ length_{B_𝔮}(B_𝔮/xB_𝔮) = ∏_v Norm_{κ(v)/κ(𝔮)}(λ) ^ length(C_v / x C_v)`

along it gives the same identity with the product taken over the maximal ideals of `C` above `𝔮`
and the norms taken from the residue fields `κ(𝔯)` of the local rings of `C`.

## Main definitions

* `Stacks.Chow.fibreLocalRingHom` — the map `D_𝔮 → E_𝔯` of local rings induced by `D → E`.
* `Stacks.Chow.fibreLocalizationAlgEquiv` — the local ring of `C` at the prime below a maximal
  ideal of the semilocalization at `𝔮`, as an algebra over `B_𝔮`.
* `Stacks.Chow.tameSymbolTransportedParameter`,
  `Stacks.Chow.tameSymbolTransportedFactorUnit`,
  `Stacks.Chow.tameSymbolTransportedExponent` — the transported preparation data.
* `Stacks.Chow.tameSymbolPreparationComp` — the transported tame-symbol preparation.

## Main results

* `Stacks.Chow.ord_of_ringEquiv`, `Stacks.Chow.ord_toNat_of_ringEquiv` — the order of vanishing is
  invariant under a ring equivalence.
* `Stacks.Chow.norm_residueField_mapAlgEquiv`,
  `Stacks.Chow.units_map_norm_residueField_mapAlgEquiv` — the residue-field norm is invariant
  under a local algebra equivalence.
* `Stacks.Chow.isLocalHom_algebraMap_localizationAtPrime` — for an integral extension of a local
  ring, the map to the localization at a maximal ideal is local.
* `Stacks.Chow.ord_toNat_localizationAtPrimeUnder`,
  `Stacks.Chow.units_map_norm_pow_localizationAtPrimeUnder` — the order of vanishing and the
  residue-field norm agree at the two models of the local ring at a maximal ideal of `C` over `𝔮`.
* `Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow_fibre` — the norm identity for an element of
  `κ(𝔮)`, with the product taken over the maximal ideals of `C` above `𝔮`.

## Implementation notes

The algebra structure of `C_𝔯` over `B_𝔮` is Mathlib's `Localization.AtPrime.algebraOfLiesOver`,
which is not an instance; statements that need it take it as an instance binder together with
`Localization.AtPrime.IsLiesOverAlgebra`, in the style of Mathlib's own lemmas about that
structure. The map `B_𝔮 → C_𝔯` is `Localization.localRingHom`, which is available without any
algebra structure at all, and is what the transport of preparation data uses.

`AlgebraicGeometry.TameSymbolPreparation` has no field asserting that the maximal ideal of the
base is not an associated prime of the extension, and none is added here: the three facts a
transported preparation cannot derive — injectivity of `B → C`, the annihilation of `C/A` by a
power of `𝔪`, and the regularity of the transported parameter — are explicit hypotheses of
`Stacks.Chow.tameSymbolPreparationComp`, and the non-associated-prime hypothesis of
`Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow` stays an explicit hypothesis of
`Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow_fibre`.

## References

* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

namespace Stacks.Chow

section OrdRingEquiv

/-- The order of vanishing of a ring element is invariant under a ring equivalence. -/
theorem ord_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hE : (R ⧸ Ideal.span {x}) ≃ₐ[R] (S ⧸ Ideal.span {e x}) :=
    Ideal.quotientEquivAlg _ _ { e with commutes' := fun _ => rfl }
      (by
        simp only [Ideal.map_span, Set.image_singleton]
        rfl)
  rw [Ring.ord, Ring.ord,
    ← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e x}) e.surjective]
  exact LinearEquiv.length_eq hE.toLinearEquiv.symm

/-- The truncated order of vanishing of a ring element is invariant under a ring equivalence. -/
theorem ord_toNat_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    (Ring.ord S (e x)).toNat = (Ring.ord R x).toNat :=
  congrArg ENat.toNat (ord_of_ringEquiv e x)

end OrdRingEquiv

section ResidueFieldTransport

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing R] [IsLocalRing S]
  [IsLocalRing T] [Algebra R S] [Algebra R T] [IsLocalHom (algebraMap R S)]
  [IsLocalHom (algebraMap R T)]

/-- **The residue-field norm is invariant under a local algebra equivalence.** An `R`-algebra
equivalence `S ≃ₐ[R] T` of local rings over a local ring `R` induces a `κ(R)`-algebra equivalence
`κ(S) ≃ₐ[κ(R)] κ(T)`, and the norm of `κ(T)/κ(R)` of an image is the norm of `κ(S)/κ(R)`. -/
theorem norm_residueField_mapAlgEquiv (e : S ≃ₐ[R] T) (x : ResidueField S) :
    Algebra.norm (ResidueField R) (ResidueField.mapAlgEquiv' e x) =
      Algebra.norm (ResidueField R) x :=
  Algebra.norm_eq_of_algEquiv (ResidueField.mapAlgEquiv' e) x

/-- The residue-field norm is invariant under a local algebra equivalence, on units. -/
theorem units_map_norm_residueField_mapAlgEquiv (e : S ≃ₐ[R] T) (x : (ResidueField S)ˣ) :
    Units.map (Algebra.norm (ResidueField R) : ResidueField T →* ResidueField R)
        (Units.map (ResidueField.mapAlgEquiv' e : ResidueField S →* ResidueField T) x) =
      Units.map (Algebra.norm (ResidueField R) : ResidueField S →* ResidueField R) x :=
  Units.ext (norm_residueField_mapAlgEquiv e x)

/-- The induced equivalence of residue fields carries the image of an element of the base residue
field to its image. -/
theorem mapAlgEquiv'_algebraMap_residueField (e : S ≃ₐ[R] T) (y : ResidueField R) :
    ResidueField.mapAlgEquiv' e (algebraMap (ResidueField R) (ResidueField S) y) =
      algebraMap (ResidueField R) (ResidueField T) y :=
  (ResidueField.mapAlgEquiv' e).commutes y

/-- The induced equivalence of residue fields carries the image of a unit of the base residue
field to its image. -/
theorem units_map_mapAlgEquiv'_algebraMap_residueField (e : S ≃ₐ[R] T) (y : (ResidueField R)ˣ) :
    Units.map (ResidueField.mapAlgEquiv' e : ResidueField S →* ResidueField T)
        (Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom y) =
      Units.map (algebraMap (ResidueField R) (ResidueField T)).toMonoidHom y :=
  Units.ext (mapAlgEquiv'_algebraMap_residueField e y)

end ResidueFieldTransport

section LocalHom

/-- For an integral extension `A → B` of a local ring and a maximal ideal `q` of `B`, the structure
map `A → B_q` is local: the maximal ideal of `B_q` contracts to `q`, which contracts to a maximal
ideal of `A`. -/
theorem isLocalHom_algebraMap_localizationAtPrime {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := by
  apply ((local_hom_TFAE (algebraMap A (Localization.AtPrime q))).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q), ← Ideal.comap_comap]
  change ((maximalIdeal (Localization.AtPrime q)).under B).comap (algebraMap A B) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal _ q]
  exact eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)

end LocalHom

section Fibre

variable {B : Type*} [CommRing B] {C : Type*} [CommRing C] [Algebra B C]
  [Algebra.IsIntegral B C] (q : MaximalSpectrum B)
  (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))

/-- A maximal ideal of the semilocalization of `C` at `𝔮` contracts to a prime of `C` lying over
`𝔮`. -/
instance liesOver_under_semilocalization : (v.asIdeal.under C).LiesOver q.asIdeal :=
  haveI := q.isMaximal
  ⟨(IsLocalization.under_under_eq_of_isMaximal q.asIdeal v.asIdeal).symm⟩

variable [Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
  [IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]

/-- The structure map `B_𝔮 → C_𝔯` of local rings along the fibre is local. -/
instance isLocalHom_fibreAlgebraMap :
    IsLocalHom (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (v.asIdeal.under C))) := by
  rw [Localization.AtPrime.algebraMap_eq]
  exact Localization.isLocalHom_localRingHom _ _ _ _

/-- **The local ring of `C` at the prime below `v`, as an algebra over `B_𝔮`.** It is the local
ring of the semilocalization of `C` at `𝔮` at the maximal ideal `v`. -/
noncomputable def fibreLocalizationAlgEquiv :
    Localization.AtPrime (v.asIdeal.under C) ≃ₐ[Localization.AtPrime q.asIdeal]
      Localization.AtPrime v.asIdeal :=
  AlgEquiv.ofRingEquiv (f := (localizationAtPrimeUnderAlgEquiv B C q v).toRingEquiv) <| by
    refine DFunLike.congr_fun (IsLocalization.ringHom_ext (S := Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl
      (j := (localizationAtPrimeUnderAlgEquiv B C q v).toAlgHom.toRingHom.comp
        (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (v.asIdeal.under C))))
      (k := algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime v.asIdeal)) ?_)
    ext b
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe]
    rw [← IsScalarTower.algebraMap_apply B (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (v.asIdeal.under C)),
      IsScalarTower.algebraMap_apply B C (Localization.AtPrime (v.asIdeal.under C)),
      ← IsScalarTower.algebraMap_apply B (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime v.asIdeal),
      IsScalarTower.algebraMap_apply B C (Localization.AtPrime v.asIdeal)]
    exact (localizationAtPrimeUnderAlgEquiv B C q v).commutes ((algebraMap B C) b)

omit [Algebra.IsIntegral B C] in
/-- `fibreLocalizationAlgEquiv` commutes with the structure maps from `B_𝔮`. -/
@[simp]
theorem fibreLocalizationAlgEquiv_algebraMap (x : Localization.AtPrime q.asIdeal) :
    fibreLocalizationAlgEquiv q v
        (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (v.asIdeal.under C)) x) =
      algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime v.asIdeal) x :=
  (fibreLocalizationAlgEquiv q v).commutes x

variable [Module.Finite B C]

/-- The structure map `B_𝔮 → (C_𝔮)_v` of local rings is local. -/
instance isLocalHom_algebraMap_localizationAtPrime_semilocalization :
    IsLocalHom (algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime v.asIdeal)) :=
  isLocalHom_algebraMap_localizationAtPrime v.asIdeal

omit [Module.Finite B C] [Algebra.IsIntegral B C] in
/-- **The order of vanishing agrees at the two models of the local ring at `𝔯`.** -/
theorem ord_toNat_localizationAtPrimeUnder (x : Localization.AtPrime q.asIdeal) :
    (Ring.ord (Localization.AtPrime v.asIdeal)
        (algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime v.asIdeal) x)).toNat =
      (Ring.ord (Localization.AtPrime (v.asIdeal.under C))
        (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (v.asIdeal.under C)) x)).toNat := by
  rw [← fibreLocalizationAlgEquiv_algebraMap q v x]
  exact ord_toNat_of_ringEquiv (fibreLocalizationAlgEquiv q v).toRingEquiv _

/-- **The residue-field norm down to `κ(𝔮)` of a power of the image of a unit of `κ(𝔮)` agrees at
the two models of the local ring at `𝔯`.** -/
theorem units_map_norm_pow_localizationAtPrimeUnder
    (lam : (ResidueField (Localization.AtPrime q.asIdeal))ˣ) (n : ℕ) :
    Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
        ResidueField (Localization.AtPrime v.asIdeal) →*
          ResidueField (Localization.AtPrime q.asIdeal))
        (Units.map (algebraMap (ResidueField (Localization.AtPrime q.asIdeal))
          (ResidueField (Localization.AtPrime v.asIdeal))).toMonoidHom lam ^ n) =
      Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
          ResidueField (Localization.AtPrime (v.asIdeal.under C)) →*
            ResidueField (Localization.AtPrime q.asIdeal))
        (Units.map (algebraMap (ResidueField (Localization.AtPrime q.asIdeal))
          (ResidueField (Localization.AtPrime (v.asIdeal.under C)))).toMonoidHom lam ^ n) := by
  rw [← units_map_mapAlgEquiv'_algebraMap_residueField (fibreLocalizationAlgEquiv q v) lam,
    ← map_pow, units_map_norm_residueField_mapAlgEquiv]

end Fibre

section FibreProduct

variable {B : Type*} [CommRing B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
  {C : Type*} [CommRing C] [Algebra B C] [Module.Finite B C] [Algebra.IsIntegral B C]
  (q : MaximalSpectrum B)
  [Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
  [∀ v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
    Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
  [∀ v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
    IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]

/-- **The identity to which the comparison of two extensions reduces, over the fibre.** For a unit
`λ` of `κ(𝔮)` and a nonzerodivisor `x` of `B_𝔮`, `λ ^ length_{B_𝔮}(B_𝔮/xB_𝔮)` is the product of
`Norm_{κ(𝔯)/κ(𝔮)}(λ) ^ length_{C_𝔯}(C_𝔯/xC_𝔯)` over the maximal ideals `𝔯` of `C` above `𝔮`. -/
theorem pow_ord_toNat_eq_prod_norm_pow_fibre
    (hass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hinj : Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquot : ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
      (⊤ : Submodule (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
      LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (lam : (ResidueField (Localization.AtPrime q.asIdeal))ˣ)
    {x : Localization.AtPrime q.asIdeal}
    (hx : x ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal)) :
    lam ^ (Ring.ord (Localization.AtPrime q.asIdeal) x).toNat =
      ∏ v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
        Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
            ResidueField (Localization.AtPrime (v.asIdeal.under C)) →*
              ResidueField (Localization.AtPrime q.asIdeal))
          (Units.map (algebraMap (ResidueField (Localization.AtPrime q.asIdeal))
              (ResidueField (Localization.AtPrime (v.asIdeal.under C)))).toMonoidHom lam ^
            (Ring.ord (Localization.AtPrime (v.asIdeal.under C))
              (algebraMap (Localization.AtPrime q.asIdeal)
                (Localization.AtPrime (v.asIdeal.under C)) x)).toNat) := by
  have := krullDimLE_one_localizationAtPrime q.asIdeal
  rw [pow_ord_toNat_eq_prod_norm_pow hass hinj hquot lam hx]
  exact Finset.prod_congr rfl fun v _ => by
    rw [ord_toNat_localizationAtPrimeUnder q v x,
      units_map_norm_pow_localizationAtPrimeUnder q v lam]

end FibreProduct

section PreparationTransport

variable {A : Type*} [CommRing A] [IsLocalRing A] {D : Type*} [CommRing D] [Algebra A D]
  {E : Type*} [CommRing E] [Algebra D E] [Algebra A E] [IsScalarTower A D E]
  [Algebra.IsIntegral D E] {r : ℕ} {a : Fin r → A}

/-- The map of local rings `D_𝔮 → E_𝔯` induced by `D → E`, where `𝔮` is the prime of `D` below the
prime `𝔯` of `E`. -/
noncomputable def fibreLocalRingHom (s : Ideal E) [s.IsPrime] :
    Localization.AtPrime (s.under D) →+* Localization.AtPrime s :=
  Localization.localRingHom (s.under D) s (algebraMap D E) rfl

omit [Algebra.IsIntegral D E] in
/-- `fibreLocalRingHom` sends the image of `d ∈ D` in `D_𝔮` to the image of `d` in `E_𝔯`. -/
@[simp]
theorem fibreLocalRingHom_algebraMap (s : Ideal E) [s.IsPrime] (d : D) :
    fibreLocalRingHom (D := D) s (algebraMap D (Localization.AtPrime (s.under D)) d) =
      algebraMap E (Localization.AtPrime s) (algebraMap D E d) :=
  Localization.localRingHom_to_map _ _ _ _ d

variable (P : TameSymbolPreparation a D)

/-- The transported parameter at a maximal ideal `𝔯` of `E`: the image of the parameter at the
maximal ideal of `D` below `𝔯`. -/
noncomputable def tameSymbolTransportedParameter (s : Ideal E) [s.IsMaximal] :
    Localization.AtPrime s :=
  letI : (s.under D).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal s
  fibreLocalRingHom (D := D) s (P.parameter (s.under D))

/-- The transported unit at a maximal ideal `𝔯` of `E`: the image of the unit at the maximal ideal
of `D` below `𝔯`. -/
noncomputable def tameSymbolTransportedFactorUnit (s : Ideal E) [s.IsMaximal] :
    Fin r → (Localization.AtPrime s)ˣ :=
  letI : (s.under D).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal s
  fun i => Units.map (fibreLocalRingHom (D := D) s).toMonoidHom (P.factorUnit (s.under D) i)

/-- The transported exponent at a maximal ideal `𝔯` of `E`: the exponent at the maximal ideal of
`D` below `𝔯`. -/
noncomputable def tameSymbolTransportedExponent (s : Ideal E) [s.IsMaximal] : Fin r → ℕ :=
  letI : (s.under D).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal s
  fun i => P.exponent (s.under D) i

/-- **Strong-form transport of a tame-symbol preparation along a tower.** For `A ⊆ D ⊆ E` with `E`
finite and integral over `D`, a preparation of a family over `D` gives a preparation of the same
family over `E` whose parameter, units and exponents at `𝔯` are those at `𝔯 ∩ D`, transported. -/
noncomputable def tameSymbolPreparationComp [Module.Finite D E]
    (hinj : Function.Injective (algebraMap D E))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A E) ≤
      LinearMap.range (Algebra.linearMap A E))
    (hreg : ∀ (s : Ideal E) (_ : s.IsMaximal), IsRegular (tameSymbolTransportedParameter P s)) :
    TameSymbolPreparation a E where
  finite := letI := P.finite; Module.Finite.trans D E
  algebraMap_injective := by
    rw [IsScalarTower.algebraMap_eq A D E]
    exact hinj.comp P.algebraMap_injective
  quotient_annihilated_by_maximalIdeal_power := hquot
  parameter s _ := tameSymbolTransportedParameter P s
  parameter_isRegular s hs := hreg s hs
  factorUnit s _ := tameSymbolTransportedFactorUnit P s
  exponent s _ := tameSymbolTransportedExponent P s
  factorization s hs i := by
    have : (s.under D).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal s
    have h := congrArg (fibreLocalRingHom (D := D) s) (P.factorization (s.under D) i)
    simp only [map_mul, map_pow, fibreLocalRingHom_algebraMap] at h
    rwa [← IsScalarTower.algebraMap_apply A D E] at h

/-- The transported preparation has the transported data: its parameter at a maximal ideal `𝔯` of
`E` is the image of the parameter at the maximal ideal of `D` below `𝔯`. -/
theorem tameSymbolPreparationComp_parameter [Module.Finite D E]
    (hinj : Function.Injective (algebraMap D E))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A E) ≤
      LinearMap.range (Algebra.linearMap A E))
    (hreg : ∀ (s : Ideal E) (_ : s.IsMaximal), IsRegular (tameSymbolTransportedParameter P s))
    (s : Ideal E) [hs : s.IsMaximal] :
    (tameSymbolPreparationComp P hinj hquot hreg).parameter s =
      tameSymbolTransportedParameter P s := rfl

/-- The transported preparation has the transported exponents. -/
theorem tameSymbolPreparationComp_exponent [Module.Finite D E]
    (hinj : Function.Injective (algebraMap D E))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A E) ≤
      LinearMap.range (Algebra.linearMap A E))
    (hreg : ∀ (s : Ideal E) (_ : s.IsMaximal), IsRegular (tameSymbolTransportedParameter P s))
    (s : Ideal E) [hs : s.IsMaximal] :
    (tameSymbolPreparationComp P hinj hquot hreg).exponent s =
      tameSymbolTransportedExponent P s := rfl

end PreparationTransport

end Stacks.Chow

end
