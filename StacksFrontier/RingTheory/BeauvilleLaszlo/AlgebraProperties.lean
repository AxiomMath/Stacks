module

public import StacksFrontier.RingTheory.BeauvilleLaszlo.Descent
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Surjectivity

/-!
# Properties of an algebra over a glueing pair detected after base change

Let `R` be a commutative ring, let `f : R` and let `R → R'` induce isomorphisms
`R/fⁿR → R'/fⁿR'` for every `n > 0`. An `R`-algebra `A` has two base changes along this data,
the localization `A_f` and the scalar extension `A ⊗[R] R'`, and so does any `A`-module and any
homomorphism of `R`-algebras out of `A`. This file collects the properties of such a
homomorphism, or of such a module, that are detected by the two base changes.

For a homomorphism `A → B` of `R`-algebras with `A` and `B` glueable for `(R → R', f)`, each of
finiteness, surjectivity, flatness, finite type, flatness together with finite presentation, and
étaleness holds for `A → B` exactly when it holds for both `A_f → B_f` and
`A ⊗[R] R' → B ⊗[R] R'`.

## Main results

* `BeauvilleLaszlo.surjective_iff_baseChange_and_awayMap_surjective`: a homomorphism of
  `R`-algebras is surjective if and only if both of its base changes are surjective.
* `BeauvilleLaszlo.quotientPowMap_tensorRight_bijective`: the ring map `A → A ⊗[R] R'` again
  induces isomorphisms `A/fⁿA → (A ⊗[R] R')/fⁿ(A ⊗[R] R')`, so the standing hypothesis on
  `R → R'` is inherited by every `R`-algebra.
* `BeauvilleLaszlo.isGlueingPair_tensorRight`: an `R`-algebra `A` glueable for `(R → R', f)`
  is itself the base of a glueing pair, namely `(A → A ⊗[R] R', f)`.
* `BeauvilleLaszlo.finite_iff_tensorRight_and_localizedModule`: an `A`-module is finite if and
  only if its scalar extension to `A ⊗[R] R'` and its localization away from the image of `f`
  are finite.
* `BeauvilleLaszlo.flat_iff_tensorRight_and_localizedModule`: for glueable `A` the same
  criterion holds for flatness.
* `BeauvilleLaszlo.finite_iff_baseChange_and_awayMap_finite` and
  `BeauvilleLaszlo.flat_iff_baseChange_and_awayMap_flat`: the same two criteria read for a
  homomorphism of `R`-algebras rather than for a module.
* `BeauvilleLaszlo.finiteType_iff_baseChange_and_awayMap_finiteType`: a homomorphism of
  `R`-algebras is of finite type if and only if both of its base changes are.
* `BeauvilleLaszlo.finitePresentation_of_baseChange_and_awayMap`: a flat homomorphism of finite
  type is of finite presentation once both of its base changes are.
* `BeauvilleLaszlo.flat_and_finitePresentation_iff_baseChange_and_awayMap`: for glueable `A`, a
  homomorphism out of `A` is flat and of finite presentation if and only if both of its base
  changes are.
* `BeauvilleLaszlo.subsingleton_of_tensorRight_and_localizedModule`: an `A`-module both of
  whose base changes vanish is zero.
* `BeauvilleLaszlo.formallyUnramified_iff_baseChange_and_awayMap`: formal unramifiedness of an
  algebra over `A` is detected by its two base changes.
* `BeauvilleLaszlo.etale_of_baseChange_and_awayMap`: étaleness descends along the two base
  changes once flatness and finite presentation do.
* `BeauvilleLaszlo.etale_iff_baseChange_and_awayMap_etale`: for glueable `A`, a homomorphism out
  of `A` is étale if and only if both of its base changes are.
* `BeauvilleLaszlo.exists_unique_algHom_of_isGlueableFor`: a glueable algebra is the fibre
  product of its two base changes, so a compatible pair of homomorphisms into those descends to
  a unique homomorphism into the algebra itself.

## References

* [Stacks Project, Tag 0BNL](https://stacks.math.columbia.edu/tag/0BNL)
* [Stacks Project, Tag 0BNN](https://stacks.math.columbia.edu/tag/0BNN)
* [Stacks Project, Tag 0BNR](https://stacks.math.columbia.edu/tag/0BNR)
* [Stacks Project, Tag 0BNW](https://stacks.math.columbia.edu/tag/0BNW)
* [Stacks Project, Tag 0BP7](https://stacks.math.columbia.edu/tag/0BP7)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
-/

universe u v w x

@[expose] public section

namespace BeauvilleLaszlo

open scoped TensorProduct

variable {R : Type u} {R' : Type v} {A : Type w}
  [CommRing R] [CommRing R'] [CommRing A] [Algebra R R'] [Algebra R A]

/-- An `R`-algebra homomorphism is surjective if and only if it becomes surjective both after
localization away from `f` and after extension of scalars to `R'`, where `(R → R', f)` is a
glueing pair. -/
theorem surjective_iff_baseChange_and_awayMap_surjective {B : Type x} [CommRing B] [Algebra R B]
    (f : R) (hglue : IsGlueingPair (algebraMap R R') f) (φ : A →ₐ[R] B) :
    Function.Surjective φ ↔
      Function.Surjective (Localization.awayMap φ.toRingHom (algebraMap R A f)) ∧
        Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id R R')) := by
  refine ⟨fun hφ => ⟨?_, ?_⟩, fun h =>
    surjective_of_baseChange_and_awayMap_surjective f hglue φ h.1 h.2⟩
  · rw [Localization.awayMap_surjective_iff]
    intro b
    obtain ⟨a, ha⟩ := hφ b
    exact ⟨a, 0, by simpa using ha⟩
  · exact Algebra.TensorProduct.map_surjective φ (AlgHom.id R R') hφ fun x => ⟨x, rfl⟩

section BaseChange

/-- The extension of the ideal `fⁿR` along a ring map `φ` is the ideal `φ(f)ⁿ`. -/
private theorem map_span_pow {S : Type*} [CommRing S] (φ : R →+* S) (f : R) (n : ℕ) :
    ((Ideal.span {f}) ^ n).map φ = (Ideal.span {φ f}) ^ n := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]

/-- The map `R/fⁿR → R'/fⁿR'` of `BeauvilleLaszlo.quotientPowMap`, as a homomorphism of
`R`-algebras. -/
private def quotientPowMapₐ (f : R) (n : ℕ) :
    (R ⧸ (Ideal.span {f}) ^ n) →ₐ[R]
      (R' ⧸ (Ideal.span {algebraMap R R' f}) ^ n) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R R') (by
    rw [← Ideal.map_le_iff_le_comap]
    exact le_of_eq (map_span_pow (algebraMap R R') f n))

/-- The `R`-algebra map `R/fⁿR → R'/fⁿR'` has the same underlying function as the ring map
`BeauvilleLaszlo.quotientPowMap`. -/
private theorem quotientPowMapₐ_apply (f : R) (n : ℕ)
    (x : R ⧸ (Ideal.span {f}) ^ n) :
    quotientPowMapₐ (R' := R') f n x = quotientPowMap f n (algebraMap R R') x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- If the ring map `R → R'` induces isomorphisms `R/fⁿR → R'/fⁿR'`, then for every `R`-algebra
`A` the ring map `A → A ⊗[R] R'` induces isomorphisms `A/fⁿA → (A ⊗[R] R')/fⁿ(A ⊗[R] R')`. -/
theorem quotientPowMap_tensorRight_bijective (f : R) (n : ℕ)
    (h : Function.Bijective (quotientPowMap f n (algebraMap R R'))) :
    Function.Bijective
      (quotientPowMap (algebraMap R A f) n
        (algebraMap A (A ⊗[R] R'))) := by
  have hq : Function.Bijective (quotientPowMapₐ (R' := R') f n) := by
    have hcoe : (quotientPowMapₐ (R' := R') f n : _ → _) =
        quotientPowMap f n (algebraMap R R') := funext (quotientPowMapₐ_apply f n)
    rw [hcoe]
    exact h
  have hr : Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R')
      (algebraMap R R' f) = algebraMap A (A ⊗[R] R') (algebraMap R A f) :=
    (AlgHom.commutes _ _).trans (IsScalarTower.algebraMap_apply R A (A ⊗[R] R') f)
  have hmap : ((Ideal.span {algebraMap R R' f}) ^ n).map
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R')) =
      (Ideal.span {algebraMap A (A ⊗[R] R') (algebraMap R A f)}) ^ n := by
    rw [← hr]
    exact map_span_pow (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R')).toRingHom
      _ n
  let E : (A ⧸ (Ideal.span {algebraMap R A f}) ^ n) ≃+*
      ((A ⊗[R] R') ⧸ (Ideal.span {algebraMap A (A ⊗[R] R') (algebraMap R A f)}) ^ n) :=
    (Ideal.quotEquivOfEq (map_span_pow (algebraMap R A) f n).symm).trans <|
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A
          ((Ideal.span {f}) ^ n)).toRingEquiv.trans <|
        (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A))
            (AlgEquiv.ofBijective (quotientPowMapₐ (R' := R') f n) hq)).toRingEquiv.trans <|
          (Algebra.TensorProduct.tensorQuotientEquiv (R := R) R R' A
              ((Ideal.span {algebraMap R R' f}) ^ n)).toRingEquiv.trans
            (Ideal.quotEquivOfEq hmap)
  have key : ∀ a : A, E (Ideal.Quotient.mk _ a) =
      quotientPowMap (algebraMap R A f) n (algebraMap A (A ⊗[R] R'))
        (Ideal.Quotient.mk _ a) := by
    intro a
    have h1 : (1 : R ⧸ (Ideal.span {f}) ^ n) =
        Ideal.Quotient.mk ((Ideal.span {f}) ^ n) 1 := (map_one _).symm
    simp only [E, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, Ideal.quotEquivOfEq_mk,
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, h1,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_ofBijective,
      quotientPowMapₐ, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, quotientPowMap_mk]
    rw [map_one]
    rfl
  have hfun : (quotientPowMap (algebraMap R A f) n
      (algebraMap A (A ⊗[R] R')) : _ → _) = E := by
    funext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (key a).symm
  rw [hfun]
  exact E.bijective

/-- The hypothesis of `BeauvilleLaszlo.quotientPowMap_tensorRight_bijective` for all positive
`n`. -/
private theorem quotientPowMap_tensorRight_bijective_of_pos (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R'))) :
    ∀ n : ℕ, 0 < n → Function.Bijective
      (quotientPowMap (algebraMap R A f) n (algebraMap A (A ⊗[R] R'))) :=
  fun n hn => quotientPowMap_tensorRight_bijective f n (hquot n hn)

/-- If the map `R/fⁿR → S/fⁿS` induced by `φ : R →+* S` is bijective, then so is the map from
`R/fⁿR` to the quotient of `S` by the extension of the ideal `fⁿR`. -/
theorem quotientMap_map_pow_bijective {S : Type*} [CommRing S] (φ : R →+* S) (f : R) (n : ℕ)
    (h : Function.Bijective (quotientPowMap f n φ)) :
    Function.Bijective
      (Ideal.quotientMap (Ideal.map φ ((Ideal.span {f}) ^ n)) φ Ideal.le_comap_map) := by
  have heq := map_span_pow φ f n
  let q := Ideal.quotientMap (Ideal.map φ ((Ideal.span {f}) ^ n)) φ Ideal.le_comap_map
  have hcomp : (Ideal.quotEquivOfEq heq).toRingHom.comp q = quotientPowMap f n φ := by
    ext r
    exact Ideal.quotEquivOfEq_mk heq (φ r)
  apply (Function.Bijective.of_comp_iff' (Ideal.quotEquivOfEq heq).bijective q).mp
  change Function.Bijective ((Ideal.quotEquivOfEq heq).toRingHom.comp q)
  rwa [hcomp]

/-- The `f`-power torsion of a module over an `R`-algebra `S` is the same submodule whether the
scalar `f` is read in `R` or through its image in `S`. -/
private theorem mem_torsion'_powers_iff {S : Type*} [CommRing S]
    [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (f : R) (g : S) (hg : g = algebraMap R S f) (x : M) :
    x ∈ Submodule.torsion' S M (Submonoid.powers g) ↔
      x ∈ Submodule.torsion' R M (Submonoid.powers f) := by
  subst hg
  rw [Submodule.mem_torsion'_iff, Submodule.mem_torsion'_iff]
  have key : ∀ n : ℕ, (algebraMap R S f ^ n) • x = (f ^ n) • x := by
    intro n
    rw [← map_pow, algebraMap_smul]
  constructor
  · rintro ⟨⟨a, n, rfl⟩, ha⟩
    rw [Submonoid.smul_def] at ha
    exact ⟨⟨f ^ n, n, rfl⟩, by rw [Submonoid.smul_def, ← key n]; exact ha⟩
  · rintro ⟨⟨a, n, rfl⟩, ha⟩
    rw [Submonoid.smul_def] at ha
    exact ⟨⟨algebraMap R S f ^ n, n, rfl⟩, by rw [Submonoid.smul_def, key n]; exact ha⟩

/-- The map `A[f^∞] → (A ⊗[R] R')[f^∞]` of `BeauvilleLaszlo.tensorProductPowerTorsionMap` and
the map on `f`-power torsion induced by the ring map `A → A ⊗[R] R'` are one function read over
the two base rings `R` and `A`, so one is bijective exactly when the other is. -/
theorem powerTorsionMap_tensorRight_bijective_iff (f : R) :
    Function.Bijective
        (powerTorsionMap (algebraMap R A f) (algebraMap A (A ⊗[R] R'))) ↔
      Function.Bijective (tensorProductPowerTorsionMap (S := R') A f) := by
  let e₁ : ↥(powerTorsion (algebraMap R A f)) ≃ ↥(modulePowerTorsion A f) :=
    Equiv.subtypeEquivRight
      (mem_torsion'_powers_iff A f (algebraMap R A f) rfl)
  let e₂ : ↥(powerTorsion (algebraMap A (A ⊗[R] R') (algebraMap R A f))) ≃
      ↥(modulePowerTorsion (A ⊗[R] R') f) :=
    Equiv.subtypeEquivRight
      (mem_torsion'_powers_iff (A ⊗[R] R') f _
        (IsScalarTower.algebraMap_apply R A (A ⊗[R] R') f).symm)
  have hfun : (tensorProductPowerTorsionMap (S := R') A f : _ → _) =
      e₂ ∘ (powerTorsionMap (algebraMap R A f) (algebraMap A (A ⊗[R] R'))) ∘ e₁.symm := by
    funext y
    apply Subtype.ext
    change ((y : A) ⊗ₜ[R] (1 : R') : A ⊗[R] R') = _
    rfl
  rw [hfun, Equiv.comp_bijective, Equiv.bijective_comp]

/-- If `R → R'` induces isomorphisms `R/fⁿR → R'/fⁿR'` and the Beauville--Laszlo sequence of
the `R`-module `A` is short exact, then the ring map `A → A ⊗[R] R'` together with the image of
`f` is a glueing pair. -/
theorem isGlueingPair_tensorRight (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact) :
    IsGlueingPair (algebraMap A (A ⊗[R] R')) (algebraMap R A f) := by
  have hquotA := quotientPowMap_tensorRight_bijective_of_pos (A := A) f hquot
  refine ⟨hquotA, ?_⟩
  rw [(beauvilleLaszloSequence_exactness_iff_powerTorsionMap (algebraMap R A f)
    (algebraMap A (A ⊗[R] R')) hquotA).2.2.2.1, powerTorsionMap_tensorRight_bijective_iff]
  exact ((beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.1
    R R' A f hquot).2.2.2.1).mp hA

/-- An `R`-algebra without `f`-power torsion is glueable for a glueing pair `(R → R', f)`: its
Beauville--Laszlo sequence is short exact. -/
theorem beauvilleLaszloModuleSequence_shortExact_of_subsingleton
    (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (htors : Subsingleton (modulePowerTorsion A f)) :
    (beauvilleLaszloModuleSequence (S := R') A f).ShortExact := by
  refine ((beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.1
    R R' A f hglue.1).2.2.2.2 hglue.2).mpr fun x y _ => Subsingleton.elim x y

end BaseChange

section Properties

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'` and let `A` be an
`R`-algebra. An `A`-module is finite if and only if its scalar extension to `A ⊗[R] R'` is
finite and its localization away from the image of `f` is finite. -/
theorem finite_iff_tensorRight_and_localizedModule (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.Finite A M ↔
      Module.Finite (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) ∧
        Module.Finite (Localization.Away (algebraMap R A f))
          (LocalizedModule.Away (algebraMap R A f) M) := by
  constructor
  · exact fun _ => ⟨inferInstance, Module.Finite.equiv
      (LocalizedModule.equivTensorProduct (Submonoid.powers (algebraMap R A f)) M).symm⟩
  · rintro ⟨hS, hL⟩
    have hprod : Module.Finite
        ((A ⊗[R] R') × Localization.Away (algebraMap R A f))
        (((A ⊗[R] R') × Localization.Away (algebraMap R A f)) ⊗[A] M) := by
      have : Module.Finite (Localization.Away (algebraMap R A f))
          (Localization.Away (algebraMap R A f) ⊗[A] M) :=
        Module.Finite.equiv
          (LocalizedModule.equivTensorProduct (Submonoid.powers (algebraMap R A f)) M)
      exact finite_tensorProduct_prod_of_finite
    exact (finite_iff_tensorProduct_prod_away_of_quotientMap_bijective A
      (algebraMap R A f)).1 (A ⊗[R] R')
      (fun m hm => quotientMap_map_pow_bijective _ _ m
        (quotientPowMap_tensorRight_bijective_of_pos f hquot m hm)) M |>.2 hprod

/-- Let the `R`-algebra `A` be glueable for `(R → R', f)`. An `A`-module is flat if and only if
its scalar extension to `A ⊗[R] R'` is flat and its localization away from the image of `f` is
flat. -/
theorem flat_iff_tensorRight_and_localizedModule (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔
      Module.Flat (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) ∧
        Module.Flat (Localization.Away (algebraMap R A f))
          (LocalizedModule.Away (algebraMap R A f) M) := by
  obtain ⟨hquotA, hglueA⟩ := isGlueingPair_tensorRight (R' := R') f hquot hA
  exact flat_iff_flat_baseChange_and_localization A (A ⊗[R] R')
    (algebraMap R A f) hquotA hglueA M

end Properties

section FiniteType

variable {B : Type w} [CommRing B] [Algebra R B]

/-- For `B` an `A`-algebra through `φ`, the scalar extension of `B` to `A ⊗[R] R'` is the ring
`B ⊗[R] R'` carrying the `A ⊗[R] R'`-algebra structure of `φ ⊗ 1`. -/
private noncomputable def baseChangeAlgEquiv [Algebra A B] [IsScalarTower R A B]
    (φ : A →ₐ[R] B) (hφ : ∀ x, algebraMap A B x = φ x)
    [Algebra (A ⊗[R] R') (B ⊗[R] R')]
    (hT : ∀ x, algebraMap (A ⊗[R] R') (B ⊗[R] R') x =
      Algebra.TensorProduct.map φ (AlgHom.id R R') x) :
    ((A ⊗[R] R') ⊗[A] B) ≃ₐ[A ⊗[R] R'] B ⊗[R] R' :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.comm A (A ⊗[R] R') B).trans
      (Algebra.TensorProduct.cancelBaseChange R A A B R')).toRingEquiv) <| by
    intro x
    rw [hT]
    induction x with
    | tmul a r' => simp [Algebra.smul_def, hφ]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Finite type is stable under the base change `- ⊗[R] R'`. -/
private lemma finiteType_tensorMap (φ : A →ₐ[R] B) (hφ : φ.toRingHom.FiniteType) :
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FiniteType := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Algebra.FiniteType A B := hφ
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  change Algebra.FiniteType (A ⊗[R] R') (B ⊗[R] R')
  exact Algebra.FiniteType.equiv inferInstance
    (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl))

/-- Every element of a localization `T` of `S` away from `x` becomes, after multiplying by a power
of `x`, the image of an element of `S`. -/
private lemma exists_algebraMap_pow_mul_eq {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (x : S) [IsLocalization.Away x T] (y : T) :
    ∃ (s : S) (k : ℕ), algebraMap S T (x ^ k) * y = algebraMap S T s := by
  obtain ⟨k, s, h⟩ := IsLocalization.Away.surj x y
  exact ⟨s, k, by rw [map_pow, mul_comm]; exact h⟩

/-- If `A_f → B_f` is of finite type, a finite set `s ⊆ B` of numerators of algebra generators
of `B_f` over `A_f` has the property that localizing away from `f` any `R`-algebra whose image
in `B` contains `s` and the image of `A` already gives all of `B_f`. -/
private lemma exists_finite_surjective_awayMap (f : R) (φ : A →ₐ[R] B)
    (hL : (Localization.awayMap φ.toRingHom (algebraMap R A f)).FiniteType) :
    ∃ s : Set B, s.Finite ∧ ∀ {C : Type w} [CommRing C] [Algebra R C] (χ : C →ₐ[R] B),
      Set.range φ ∪ s ⊆ Set.range χ →
        Function.Surjective (Localization.awayMap χ.toRingHom (algebraMap R C f)) := by
  set a := algebraMap R A f with ha
  set Aa := Localization.Away a
  set Ba := Localization.Away (φ a)
  set L := Localization.awayMap φ.toRingHom a
  let _ : Algebra Aa Ba := L.toAlgebra
  have halg : ∀ x : Aa, algebraMap Aa Ba x = L x := fun _ => rfl
  have hFT : Algebra.FiniteType Aa Ba := hL
  obtain ⟨t, ht⟩ := hFT.out
  have hLalg : ∀ x : A, L (algebraMap A Aa x) = algebraMap B Ba (φ x) := fun _ =>
    IsLocalization.map_eq _ _
  choose bb kk hbb using exists_algebraMap_pow_mul_eq (T := Ba) (φ a)
  refine ⟨bb '' (t : Set Ba), (t.finite_toSet).image bb, ?_⟩
  set D := Algebra.adjoin R (Set.range φ ∪ bb '' (t : Set Ba))
  have huD : φ a ∈ D := Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  have hφD : ∀ x : A, φ x ∈ D := fun x => Algebra.subset_adjoin (Or.inl ⟨x, rfl⟩)
  have hQ : ∀ y : Ba, ∃ (c : B) (N : ℕ), c ∈ D ∧
      algebraMap B Ba (φ a ^ N) * y = algebraMap B Ba c := by
    intro y
    have hy : y ∈ Algebra.adjoin Aa (t : Set Ba) := ht ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact ⟨bb x, kk x, Algebra.subset_adjoin (Or.inr ⟨x, hx, rfl⟩), hbb x⟩
    | algebraMap r =>
        obtain ⟨α, k, hk⟩ := exists_algebraMap_pow_mul_eq (T := Aa) a r
        refine ⟨φ α, k, hφD α, ?_⟩
        have hpow : algebraMap B Ba (φ a ^ k) = L (algebraMap A Aa (a ^ k)) := by
          rw [← map_pow, hLalg]
        rw [halg, hpow, ← map_mul, hk, hLalg]
    | add x y _ _ ihx ihy =>
        obtain ⟨c₁, N₁, hc₁, h₁⟩ := ihx
        obtain ⟨c₂, N₂, hc₂, h₂⟩ := ihy
        refine ⟨φ a ^ N₂ * c₁ + φ a ^ N₁ * c₂, N₁ + N₂,
          add_mem (mul_mem (pow_mem huD N₂) hc₁) (mul_mem (pow_mem huD N₁) hc₂), ?_⟩
        have hsplit : algebraMap B Ba (φ a ^ (N₁ + N₂)) * (x + y) =
            algebraMap B Ba (φ a ^ N₂) * (algebraMap B Ba (φ a ^ N₁) * x) +
              algebraMap B Ba (φ a ^ N₁) * (algebraMap B Ba (φ a ^ N₂) * y) := by
          rw [pow_add, map_mul]; ring
        rw [hsplit, h₁, h₂, map_add, map_mul, map_mul]
    | mul x y _ _ ihx ihy =>
        obtain ⟨c₁, N₁, hc₁, h₁⟩ := ihx
        obtain ⟨c₂, N₂, hc₂, h₂⟩ := ihy
        refine ⟨c₁ * c₂, N₁ + N₂, mul_mem hc₁ hc₂, ?_⟩
        have hsplit : algebraMap B Ba (φ a ^ (N₁ + N₂)) * (x * y) =
            (algebraMap B Ba (φ a ^ N₁) * x) * (algebraMap B Ba (φ a ^ N₂) * y) := by
          rw [pow_add, map_mul]; ring
        rw [hsplit, h₁, h₂, map_mul]
  have hE : ∀ b : B, ∃ k : ℕ, φ a ^ k * b ∈ D := by
    intro b
    obtain ⟨c, N, hc, hb⟩ := hQ (algebraMap B Ba b)
    rw [← map_mul] at hb
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (φ a)) Ba).mp hb
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp w.2
    rw [← hj] at hw
    exact ⟨j + N, by rw [pow_add, mul_assoc, hw]; exact mul_mem (pow_mem huD j) hc⟩
  intro C _ _ χ hsub
  rw [Localization.awayMap_surjective_iff]
  intro b
  obtain ⟨k, hk⟩ := hE b
  obtain ⟨c, hc⟩ := (Algebra.adjoin_le hsub : D ≤ χ.range) hk
  have hχf : φ a = χ.toRingHom (algebraMap R C f) := by
    rw [ha, φ.commutes]; exact (χ.commutes f).symm
  exact ⟨c, k, by rw [hc, hχf]⟩

/-- If `A ⊗[R] R' → B ⊗[R] R'` is of finite type, then the finitely many tensor factors in `B`
of a set of algebra generators of `B ⊗[R] R'` over `A ⊗[R] R'` form a finite set `s ⊆ B` such
that base changing any `R`-algebra whose image in `B` contains `s` and the image of `A` already
gives all of `B ⊗[R] R'`. -/
private lemma exists_finite_surjective_tensorMap (φ : A →ₐ[R] B)
    (hT : (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FiniteType) :
    ∃ s : Set B, s.Finite ∧ ∀ {C : Type w} [CommRing C] [Algebra R C] (χ : C →ₐ[R] B),
      Set.range φ ∪ s ⊆ Set.range χ →
        Function.Surjective (Algebra.TensorProduct.map χ (AlgHom.id R R')) := by
  set T := Algebra.TensorProduct.map φ (AlgHom.id R R') with hTdef
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') := T.toRingHom.toAlgebra
  have halg : ∀ x : A ⊗[R] R', algebraMap (A ⊗[R] R') (B ⊗[R] R') x = T x := fun _ => rfl
  have hFT : Algebra.FiniteType (A ⊗[R] R') (B ⊗[R] R') := hT
  obtain ⟨t, ht⟩ := hFT.out
  choose kz mz nz hz using fun z : B ⊗[R] R' => TensorProduct.exists_sum_tmul_eq z
  refine ⟨⋃ z ∈ (t : Set (B ⊗[R] R')), Set.range (mz z),
    Set.Finite.biUnion t.finite_toSet fun z _ => Set.finite_range _, ?_⟩
  intro C _ _ χ hsub
  set X := Algebra.TensorProduct.map χ (AlgHom.id R R') with hX
  have hrangeT : ∀ x : A ⊗[R] R', ∃ w, X w = T x := by
    intro x
    induction x with
    | tmul α r' =>
        obtain ⟨c, hc⟩ := hsub (Or.inl ⟨α, rfl⟩)
        exact ⟨c ⊗ₜ[R] r', by simp [hX, hTdef, hc]⟩
    | add x y hx hy =>
        obtain ⟨w₁, h₁⟩ := hx
        obtain ⟨w₂, h₂⟩ := hy
        exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, map_add]⟩
  have hmem : ∀ x : B ⊗[R] R', x ∈ X.range := by
    intro x
    have hx : x ∈ Algebra.adjoin (A ⊗[R] R') (t : Set (B ⊗[R] R')) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem z hzt =>
        rw [hz z]
        refine sum_mem fun j _ => ?_
        obtain ⟨c, hc⟩ := hsub (Or.inr (Set.mem_biUnion hzt ⟨j, rfl⟩))
        exact ⟨c ⊗ₜ[R] nz z j, by simp [hX, hc]⟩
    | algebraMap r =>
        obtain ⟨w, hw⟩ := hrangeT r
        exact ⟨w, hw⟩
    | add x y _ _ ihx ihy => exact add_mem ihx ihy
    | mul x y _ _ ihx ihy => exact mul_mem ihx ihy
  exact hmem

/-- Let `(R → R', f)` be a glueing pair and let `φ : A →ₐ[R] B` be a homomorphism of
`R`-algebras. Then `φ` is of finite type if and only if both its localization away from `f` and
its base change along `R → R'` are. -/
theorem finiteType_iff_baseChange_and_awayMap_finiteType
    (f : R) (hglue : IsGlueingPair (algebraMap R R') f) (φ : A →ₐ[R] B) :
    φ.toRingHom.FiniteType ↔
      (Localization.awayMap φ.toRingHom (algebraMap R A f)).FiniteType ∧
        (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FiniteType := by
  refine ⟨fun h => ⟨?_, finiteType_tensorMap φ h⟩, fun h => ?_⟩
  · exact RingHom.localization_away_map_finiteType A B (Localization.Away (algebraMap R A f))
      (Localization.Away (φ (algebraMap R A f))) φ.toRingHom (algebraMap R A f) h
  obtain ⟨s₁, hs₁, hA⟩ := exists_finite_surjective_awayMap f φ h.1
  obtain ⟨s₂, hs₂, hB⟩ := exists_finite_surjective_tensorMap φ h.2
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let s : Set B := s₁ ∪ s₂
  have hsfin : s.Finite := hs₁.union hs₂
  let ψ₀ : MvPolynomial (↥s) A →ₐ[A] B := MvPolynomial.aeval (fun x : ↥s => (x : B))
  let ψ : MvPolynomial (↥s) A →ₐ[R] B := ψ₀.restrictScalars R
  have hsubψ : Set.range φ ∪ s ⊆ Set.range ψ := by
    rintro x (⟨α, rfl⟩ | hx)
    · refine ⟨MvPolynomial.C α, ?_⟩
      change ψ₀ (MvPolynomial.C α) = φ α
      rw [MvPolynomial.aeval_C]
      rfl
    · refine ⟨MvPolynomial.X ⟨x, hx⟩, ?_⟩
      change ψ₀ (MvPolynomial.X ⟨x, hx⟩) = x
      rw [MvPolynomial.aeval_X]
  have hsurj : Function.Surjective ψ :=
    surjective_of_baseChange_and_awayMap_surjective f hglue ψ
      (hA ψ (fun x hx => hsubψ (Or.imp_right (fun h => Or.inl h) hx)))
      (hB ψ (fun x hx => hsubψ (Or.imp_right (fun h => Or.inr h) hx)))
  have htop : Algebra.adjoin A s = ⊤ := by
    rw [Algebra.adjoin_eq_range]
    exact (AlgHom.range_eq_top ψ₀).mpr hsurj
  exact ⟨⟨hsfin.toFinset, by rwa [hsfin.coe_toFinset]⟩⟩

end FiniteType

section RingMap

variable {B : Type w} [CommRing B] [Algebra R B]

/-- For `B` an `A`-algebra through `φ`, the localization of `B` away from the image of `f` is
the ring `Localization.Away (φ f)` carrying the `A_f`-algebra structure of the localized map. -/
private noncomputable def awayLinearEquiv [Algebra A B] [IsScalarTower R A B] (f : R)
    (φ : A →ₐ[R] B) (hφ : ∀ x, algebraMap A B x = φ x)
    [Algebra (Localization.Away (algebraMap R A f)) (Localization.Away (φ (algebraMap R A f)))]
    (hL : ∀ x, algebraMap (Localization.Away (algebraMap R A f))
        (Localization.Away (φ (algebraMap R A f))) x =
      Localization.awayMap φ.toRingHom (algebraMap R A f) x) :
    LocalizedModule.Away (algebraMap R A f) B ≃ₗ[Localization.Away (algebraMap R A f)]
      Localization.Away (φ (algebraMap R A f)) := by
  have _ : IsScalarTower A (Localization.Away (algebraMap R A f))
      (Localization.Away (φ (algebraMap R A f))) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hL, IsScalarTower.algebraMap_apply A B (Localization.Away (φ (algebraMap R A f))) x, hφ]
      exact (IsLocalization.map_eq _ _).symm
  have hg : Submonoid.powers (algebraMap A B (algebraMap R A f)) =
      Submonoid.powers (φ (algebraMap R A f)) := by rw [hφ]
  have _ : IsLocalizedModule (Submonoid.powers (algebraMap A B (algebraMap R A f)))
      (Algebra.linearMap B (Localization.Away (φ (algebraMap R A f)))) := by
    rw [hg]; infer_instance
  have _ : IsLocalizedModule (Submonoid.powers (algebraMap R A f))
      ((Algebra.linearMap B (Localization.Away (φ (algebraMap R A f)))).restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers _ _
  exact LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers (algebraMap R A f))
    (Localization.Away (algebraMap R A f))
    (IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R A f))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R A f)) B)
      ((Algebra.linearMap B (Localization.Away (φ (algebraMap R A f)))).restrictScalars A))

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'`. A homomorphism of `R`-algebras is finite
if and only if both its localization away from `f` and its scalar extension to `R'` are
finite. -/
theorem finite_iff_baseChange_and_awayMap_finite (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (φ : A →ₐ[R] B) :
    φ.toRingHom.Finite ↔
      (Localization.awayMap φ.toRingHom (algebraMap R A f)).Finite ∧
        (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Finite := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  let _ : Algebra (Localization.Away (algebraMap R A f))
      (Localization.Away (φ (algebraMap R A f))) :=
    (Localization.awayMap φ.toRingHom (algebraMap R A f)).toAlgebra
  change Module.Finite A B ↔ _
  rw [finite_iff_tensorRight_and_localizedModule (R' := R') f hquot B,
    Module.Finite.equiv_iff
      (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl)).toLinearEquiv,
    Module.Finite.equiv_iff (awayLinearEquiv f φ (fun _ => rfl) (fun _ => rfl))]
  exact and_comm

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'` and let the `R`-algebra `A` be glueable
for `(R → R', f)`. A homomorphism out of `A` is flat if and only if both its localization away
from `f` and its scalar extension to `R'` are flat. -/
theorem flat_iff_baseChange_and_awayMap_flat (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact)
    (φ : A →ₐ[R] B) :
    φ.toRingHom.Flat ↔
      (Localization.awayMap φ.toRingHom (algebraMap R A f)).Flat ∧
        (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Flat := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  let _ : Algebra (Localization.Away (algebraMap R A f))
      (Localization.Away (φ (algebraMap R A f))) :=
    (Localization.awayMap φ.toRingHom (algebraMap R A f)).toAlgebra
  change Module.Flat A B ↔ _
  rw [flat_iff_tensorRight_and_localizedModule (R' := R') f hquot hA B,
    Module.Flat.equiv_iff
      (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl)).toLinearEquiv,
    Module.Flat.equiv_iff (awayLinearEquiv f φ (fun _ => rfl) (fun _ => rfl))]
  exact and_comm

/-- Flatness is stable under the base change `- ⊗[R] R'`. -/
private lemma flat_tensorMap (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Flat) :
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Flat := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Module.Flat A B := hφ
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  change Module.Flat (A ⊗[R] R') (B ⊗[R] R')
  exact Module.Flat.of_linearEquiv
    (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl)).symm.toLinearEquiv

/-- Finite presentation is stable under the base change `- ⊗[R] R'`. -/
private lemma finitePresentation_tensorMap (φ : A →ₐ[R] B)
    (hφ : φ.toRingHom.FinitePresentation) :
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FinitePresentation := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Algebra.FinitePresentation A B := hφ
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  change Algebra.FinitePresentation (A ⊗[R] R') (B ⊗[R] R')
  exact Algebra.FinitePresentation.equiv (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl))

/-- A flat homomorphism of `R`-algebras of finite presentation stays flat and of finite
presentation both after localization away from `f` and after extension of scalars to `R'`. -/
theorem flat_and_finitePresentation_baseChange_and_awayMap (f : R) (φ : A →ₐ[R] B)
    (h : φ.toRingHom.Flat ∧ φ.toRingHom.FinitePresentation) :
    ((Localization.awayMap φ.toRingHom (algebraMap R A f)).Flat ∧
        (Localization.awayMap φ.toRingHom (algebraMap R A f)).FinitePresentation) ∧
      ((Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Flat ∧
        (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FinitePresentation) :=
  ⟨⟨RingHom.Flat.propertyIsLocal.localizationAwayPreserves φ.toRingHom
      (algebraMap R A f) _ _ h.1,
    RingHom.finitePresentation_localizationPreserves.away φ.toRingHom
      (algebraMap R A f) _ _ h.2⟩,
    flat_tensorMap φ h.1, finitePresentation_tensorMap φ h.2⟩

/-- The kernel of a surjective ring map `g : Y → Z` is finitely generated when `Y` and `Z` are
finitely presented over a common ring `X` through maps compatible with `g`. -/
private lemma ker_fg_of_comp_eq {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z]
    (a : X →+* Y) (b : X →+* Z) (g : Y →+* Z) (hab : g.comp a = b)
    (hg : Function.Surjective g) (ha : a.FinitePresentation) (hb : b.FinitePresentation) :
    (RingHom.ker g).FG := by
  let _ : Algebra X Y := a.toAlgebra
  let _ : Algebra X Z := b.toAlgebra
  have _ : Algebra.FinitePresentation X Y := ha
  have _ : Algebra.FinitePresentation X Z := hb
  let g' : Y →ₐ[X] Z := { toRingHom := g, commutes' := fun x => RingHom.congr_fun hab x }
  exact Algebra.FinitePresentation.ker_fG_of_surjective g' hg

/-- Let `ψ : P → B` be a surjection of `A`-algebras with `B` flat over `A`, and let `C` be an
`A`-algebra. If the kernel of `ψ ⊗ C : P ⊗[A] C → B ⊗[A] C` is finitely generated, then the
base change of the kernel of `ψ` to `P ⊗[A] C` is a finite module. -/
private lemma finite_baseChange_ker_of_flat {A P B C : Type*} [CommRing A] [CommRing P]
    [CommRing B] [CommRing C] [Algebra A P] [Algebra A B] [Algebra A C] [Module.Flat A B]
    (ψ : P →ₐ[A] B) (hψ : Function.Surjective ψ)
    (hker : (RingHom.ker (Algebra.TensorProduct.map ψ (AlgHom.id A C)).toRingHom).FG) :
    Module.Finite (P ⊗[A] C) ((P ⊗[A] C) ⊗[P] RingHom.ker ψ.toRingHom) := by
  let I := RingHom.ker ψ.toRingHom
  let ι : I →ₗ[A] P := (Submodule.subtype I).restrictScalars A
  have hex : Function.Exact ι ψ.toLinearMap := fun y =>
    ⟨fun hy => ⟨⟨y, RingHom.mem_ker.mpr hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  have hinj : Function.Injective (ι.rTensor C) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp
      (LinearMap.lTensor_injective_of_exact_of_flat ψ.toLinearMap hψ ι Subtype.val_injective
        hex C)
  let e : (P ⊗[A] C) ⊗[P] I ≃ₗ[P] I ⊗[A] C :=
    (TensorProduct.comm P (P ⊗[A] C) I).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A P P I C)
  let κ : (P ⊗[A] C) ⊗[P] I →ₗ[P ⊗[A] C] P ⊗[A] C :=
    (TensorProduct.AlgebraTensorModule.rid P (P ⊗[A] C) (P ⊗[A] C)).toLinearMap ∘ₗ
      (Submodule.subtype I).baseChange (P ⊗[A] C)
  have hκ : ∀ x, κ x = ι.rTensor C (e x) := by
    intro x
    induction x with
    | add x y hx hy =>
      rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
    | tmul s i =>
      induction s with
      | add s t hs ht =>
        rw [TensorProduct.add_tmul, LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add,
          hs, ht]
      | tmul p c =>
        simp [κ, e, ι, TensorProduct.smul_tmul', mul_comm]
  have hκinj : Function.Injective κ := by
    intro x y hxy
    rw [hκ, hκ] at hxy
    exact e.injective (hinj hxy)
  have hrange : LinearMap.range κ =
      (RingHom.ker (Algebra.TensorProduct.map ψ (AlgHom.id A C)).toRingHom :
        Submodule (P ⊗[A] C) (P ⊗[A] C)) := by
    have hexC := rTensor_exact C hex hψ
    ext x
    rw [LinearMap.mem_range]
    change _ ↔ Algebra.TensorProduct.map ψ (AlgHom.id A C) x = 0
    have hmap : Algebra.TensorProduct.map ψ (AlgHom.id A C) x = ψ.toLinearMap.rTensor C x := by
      induction x with
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul p c => simp
    rw [hmap, hexC x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, (hκ y).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z, by rw [hκ, LinearEquiv.apply_symm_apply]⟩
  have : Module.Finite (P ⊗[A] C) (LinearMap.range κ) := by
    rw [hrange]
    exact Module.Finite.iff_fg.mpr hker
  exact Module.Finite.equiv (LinearEquiv.ofInjective κ hκinj).symm

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'` and let `φ : A → B` be a flat
homomorphism of `R`-algebras of finite type. If its localization away from `f` and its scalar
extension to `R'` are of finite presentation, so is `φ`. -/
theorem finitePresentation_of_baseChange_and_awayMap (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (φ : A →ₐ[R] B) (hflat : φ.toRingHom.Flat) (hft : φ.toRingHom.FiniteType)
    (h₁ : (Localization.awayMap φ.toRingHom (algebraMap R A f)).FinitePresentation)
    (h₂ : (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FinitePresentation) :
    φ.toRingHom.FinitePresentation := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Module.Flat A B := hflat
  have hft' : Algebra.FiniteType A B := hft
  change Algebra.FinitePresentation A B
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  refine ⟨n, ψ, hψ, ?_⟩
  have hquotA := quotientPowMap_tensorRight_bijective_of_pos (A := A) f hquot
  suffices Module.Finite (MvPolynomial (Fin n) A) (RingHom.ker ψ.toRingHom) from
    Module.Finite.iff_fg.mp this
  refine (finite_iff_tensorRight_and_localizedModule (R' := A ⊗[R] R')
    (algebraMap R A f) hquotA _).2 ⟨?_, ?_⟩
  · apply finite_baseChange_ker_of_flat ψ hψ
    let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
      (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
    have _ : Algebra.FinitePresentation (A ⊗[R] R') (B ⊗[R] R') := h₂
    have _ : Algebra.FinitePresentation (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B) :=
      Algebra.FinitePresentation.equiv
        (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl)).symm
    let eP := (Algebra.TensorProduct.comm A (A ⊗[R] R') (MvPolynomial (Fin n) A)).toRingEquiv
    let eB := (Algebra.TensorProduct.comm A (A ⊗[R] R') B).toRingEquiv
    refine ker_fg_of_comp_eq
      (eP.toRingHom.comp (algebraMap (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] MvPolynomial (Fin n) A)))
      (eB.toRingHom.comp (algebraMap (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B))) _ ?_
      (Algebra.TensorProduct.map_surjective ψ (AlgHom.id A (A ⊗[R] R')) hψ fun x => ⟨x, rfl⟩)
      (RingHom.finitePresentation_respectsIso.1 _ _
        (RingHom.finitePresentation_algebraMap.mpr inferInstance))
      (RingHom.finitePresentation_respectsIso.1 _ _
        (RingHom.finitePresentation_algebraMap.mpr inferInstance))
    refine RingHom.ext fun x => ?_
    simp [eP, eB, Algebra.TensorProduct.algebraMap_apply]
  · let g := algebraMap R A f
    let P := MvPolynomial (Fin n) A
    let M := Submonoid.powers (algebraMap A P g)
    let Q := Localization.Away (φ g)
    have hT : Submonoid.map ψ.toRingHom M = Submonoid.powers (φ g) := by
      rw [Submonoid.map_powers]
      exact congrArg _ (ψ.commutes g)
    have _ : IsLocalization (Submonoid.map ψ.toRingHom M) Q := by
      rw [hT]
      infer_instance
    let k : RingHom.ker ψ.toRingHom →ₗ[P] RingHom.ker
        (IsLocalization.map Q ψ.toRingHom M.le_comap_map :
          Localization.Away (algebraMap A P g) →+* Q) :=
      RingHom.toKerIsLocalization (Localization.Away (algebraMap A P g)) Q ψ.toRingHom
        M.le_comap_map
    have hk : IsLocalizedModule M k :=
      RingHom.toKerIsLocalization_isLocalizedModule (S := Localization.Away (algebraMap A P g))
        Q ψ.toRingHom rfl
    have hfg : (RingHom.ker (IsLocalization.map Q ψ.toRingHom M.le_comap_map :
        Localization.Away (algebraMap A P g) →+* Q)).FG := by
      refine ker_fg_of_comp_eq (Localization.awayMap (algebraMap A P) g)
        (Localization.awayMap φ.toRingHom g) _ ?_
        (IsLocalization.map_surjective_of_surjective M _ Q hψ)
        (RingHom.finitePresentation_localizationPreserves.away (algebraMap A P) g _ _
          (RingHom.finitePresentation_algebraMap.mpr inferInstance)) h₁
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq]
      exact (IsLocalization.map_eq _ _).trans (congrArg (algebraMap B Q) (ψ.commutes a))
    have _ : Module.Finite (Localization.Away (algebraMap A P g)) (RingHom.ker
        (IsLocalization.map Q ψ.toRingHom M.le_comap_map :
          Localization.Away (algebraMap A P g) →+* Q)) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (LinearEquiv.extendScalarsOfIsLocalization M
      (Localization.Away (algebraMap A P g)) (IsLocalizedModule.iso M k)).symm

/-- Let `(R → R', f)` be a glueing pair and let the `R`-algebra `A` be glueable for it. A
homomorphism out of `A` is flat and of finite presentation if and only if both its localization
away from `f` and its scalar extension to `R'` are. -/
theorem flat_and_finitePresentation_iff_baseChange_and_awayMap (f : R)
    (hglue : IsGlueingPair (algebraMap R R') f)
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact) (φ : A →ₐ[R] B) :
    (φ.toRingHom.Flat ∧ φ.toRingHom.FinitePresentation) ↔
      ((Localization.awayMap φ.toRingHom (algebraMap R A f)).Flat ∧
          (Localization.awayMap φ.toRingHom (algebraMap R A f)).FinitePresentation) ∧
        ((Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Flat ∧
          (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.FinitePresentation) := by
  refine ⟨flat_and_finitePresentation_baseChange_and_awayMap f φ, fun h => ?_⟩
  have hflat : φ.toRingHom.Flat :=
    (flat_iff_baseChange_and_awayMap_flat f hglue.1 hA φ).2 ⟨h.1.1, h.2.1⟩
  have hft : φ.toRingHom.FiniteType :=
    (finiteType_iff_baseChange_and_awayMap_finiteType f hglue φ).2
      ⟨.of_finitePresentation h.1.2, .of_finitePresentation h.2.2⟩
  exact ⟨hflat, finitePresentation_of_baseChange_and_awayMap f hglue.1 φ hflat hft h.1.2 h.2.2⟩

end RingMap

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'` and let `A` be an `R`-algebra. An
`A`-module whose scalar extension to `A ⊗[R] R'` and whose localization away from the image of
`f` both vanish is itself zero. -/
theorem subsingleton_of_tensorRight_and_localizedModule (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (M : Type*) [AddCommGroup M] [Module A M]
    (h₁ : Subsingleton ((A ⊗[R] R') ⊗[A] M))
    (h₂ : Subsingleton (LocalizedModule.Away (algebraMap R A f) M)) :
    Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  have hdetect : Nontrivial (M ⊗[A] ((A ⊗[R] R') × Localization.Away (algebraMap R A f))) :=
    (tensorProduct_prod_away_nontrivial_of_quotientMap_bijective A (algebraMap R A f)).1
      (A ⊗[R] R') (fun m hm => quotientMap_map_pow_bijective _ _ m
        (quotientPowMap_tensorRight_bijective_of_pos f hquot m hm)) M
  have hS : Subsingleton (M ⊗[A] (A ⊗[R] R')) :=
    Equiv.subsingleton (TensorProduct.comm A M (A ⊗[R] R')).toEquiv
  have hL : Subsingleton (M ⊗[A] Localization.Away (algebraMap R A f)) := by
    have hbc : IsBaseChange (Localization.Away (algebraMap R A f))
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R A f)) M) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R A f))
        (Localization.Away (algebraMap R A f)) _).mp inferInstance
    have : Subsingleton (Localization.Away (algebraMap R A f) ⊗[A] M) :=
      Equiv.subsingleton hbc.equiv.toEquiv
    exact Equiv.subsingleton (TensorProduct.comm A M _).toEquiv
  have hprod : Subsingleton ((M ⊗[A] (A ⊗[R] R')) ×
      (M ⊗[A] Localization.Away (algebraMap R A f))) :=
    ⟨fun x y => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  exact absurd (Equiv.subsingleton
    (TensorProduct.prodRight A A M (A ⊗[R] R')
      (Localization.Away (algebraMap R A f))).toEquiv) (not_subsingleton _)

section Unramified

variable {B : Type x} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {B' Aₘ Bₘ : Type*} [CommRing B'] [CommRing Aₘ] [CommRing Bₘ]
  [Algebra A B'] [Algebra (A ⊗[R] R') B'] [Algebra B B']
  [IsScalarTower A (A ⊗[R] R') B'] [IsScalarTower A B B']
  [Algebra.IsPushout A (A ⊗[R] R') B B']
  [Algebra A Aₘ] [Algebra A Bₘ] [Algebra B Bₘ] [Algebra Aₘ Bₘ]
  [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'`, let `B` be an algebra over an
`R`-algebra `A`, let `B'` be the base change of `B` along `A → A ⊗[R] R'` and let `A_f → B_f` be
the localizations away from the image of `f`. If `A ⊗[R] R' → B'` and `A_f → B_f` are formally
unramified then so is `A → B`. -/
theorem formallyUnramified_of_baseChange_and_awayMap (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    [IsLocalization.Away (algebraMap R A f) Aₘ]
    [IsLocalization.Away (algebraMap R B f) Bₘ]
    (h₁ : Algebra.FormallyUnramified (A ⊗[R] R') B')
    (h₂ : Algebra.FormallyUnramified Aₘ Bₘ) :
    Algebra.FormallyUnramified A B := by
  have hBₘ : IsLocalization
      (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f))) Bₘ := by
    rw [Algebra.algebraMapSubmonoid_powers, ← IsScalarTower.algebraMap_apply]
    infer_instance
  rw [Algebra.formallyUnramified_iff]
  refine subsingleton_of_tensorRight_and_localizedModule (A := A) f hquot Ω[B⁄A] ?_ ?_
  · have := h₁.subsingleton_kaehlerDifferential
    exact Equiv.subsingleton
      (KaehlerDifferential.tensorKaehlerEquivBase A (A ⊗[R] R') B B').toEquiv
  · have := h₂.subsingleton_kaehlerDifferential
    have hloc : IsLocalizedModule (Submonoid.powers (algebraMap R A f))
        ((KaehlerDifferential.map A Aₘ B Bₘ).restrictScalars A) :=
      KaehlerDifferential.isLocalizedModule A Aₘ B Bₘ _
    exact Equiv.subsingleton (IsLocalizedModule.iso _
      ((KaehlerDifferential.map A Aₘ B Bₘ).restrictScalars A)).toEquiv

omit [Algebra R B] [IsScalarTower R A B] in
/-- Formal unramifiedness of `A → B` is inherited by the base change along `A → A ⊗[R] R'`, for
`B'` any pushout of `B` along that map. -/
theorem formallyUnramified_baseChange [Algebra.FormallyUnramified A B] :
    Algebra.FormallyUnramified (A ⊗[R] R') B' :=
  have : Algebra.FormallyUnramified (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B) := inferInstance
  .of_equiv (Algebra.IsPushout.equiv A (A ⊗[R] R') B B')

/-- Formal unramifiedness of `A → B` is inherited by the localizations away from the image
of `f`. -/
theorem formallyUnramified_awayMap (f : R) [IsLocalization.Away (algebraMap R A f) Aₘ]
    [IsLocalization.Away (algebraMap R B f) Bₘ] [Algebra.FormallyUnramified A B] :
    Algebra.FormallyUnramified Aₘ Bₘ := by
  have hBₘ : IsLocalization
      ((Submonoid.powers (algebraMap R A f)).map (algebraMap A B)) Bₘ := by
    change IsLocalization
      (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f))) Bₘ
    rw [Algebra.algebraMapSubmonoid_powers, ← IsScalarTower.algebraMap_apply]
    infer_instance
  exact Algebra.FormallyUnramified.localization_map (S := B)
    (Submonoid.powers (algebraMap R A f))

/-- An algebra `B` over an `R`-algebra `A` is formally unramified if and only if its base change
along `A → A ⊗[R] R'` and its localization away from `f` are. -/
theorem formallyUnramified_iff_baseChange_and_awayMap (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    [IsLocalization.Away (algebraMap R A f) Aₘ]
    [IsLocalization.Away (algebraMap R B f) Bₘ] :
    Algebra.FormallyUnramified A B ↔
      Algebra.FormallyUnramified (A ⊗[R] R') B' ∧ Algebra.FormallyUnramified Aₘ Bₘ := by
  refine ⟨fun h => ?_, fun h => formallyUnramified_of_baseChange_and_awayMap f hquot h.1 h.2⟩
  have := h
  exact ⟨formallyUnramified_baseChange (A := A) (B := B),
    formallyUnramified_awayMap (A := A) (B := B) f⟩

/-- Let `R → R'` induce isomorphisms `R/fⁿR → R'/fⁿR'` and let `B` be a flat algebra of finite
presentation over an `R`-algebra `A`. If the base change `A ⊗[R] R' → B'` and the localization
`A_f → B_f` away from the image of `f` are étale, then so is `A → B`. -/
theorem etale_of_baseChange_and_awayMap (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    [IsLocalization.Away (algebraMap R A f) Aₘ]
    [IsLocalization.Away (algebraMap R B f) Bₘ]
    (hflat : Module.Flat A B) (hfp : Algebra.FinitePresentation A B)
    (h₁ : Algebra.Etale (A ⊗[R] R') B') (h₂ : Algebra.Etale Aₘ Bₘ) :
    Algebra.Etale A B := by
  have := hflat
  have := hfp
  have := h₁
  have := h₂
  have hu₁ : Algebra.FormallyUnramified (A ⊗[R] R') B' := inferInstance
  have hu₂ : Algebra.FormallyUnramified Aₘ Bₘ := inferInstance
  have : Algebra.FormallyUnramified A B :=
    formallyUnramified_of_baseChange_and_awayMap (B' := B') (Bₘ := Bₘ) f hquot hu₁ hu₂
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Unramified

section Canonical

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type x} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The powers of the image of `f` in `B` are the extension along `A → B` of the powers of the
image of `f` in `A`. -/
private theorem algebraMapSubmonoid_powers_algebraMap (f : R) :
    Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f))
      = Submonoid.powers (algebraMap R B f) := by
  rw [Algebra.algebraMapSubmonoid_powers, ← IsScalarTower.algebraMap_apply]

/-- Formal unramifiedness is detected by the two base changes of a glueing pair, for the
canonical models of those base changes: the tensor product `(A ⊗[R] R') ⊗[A] B` and the
localization of `B` at the image of the powers of `f`. -/
theorem formallyUnramified_of_tensorRight_and_localization (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (h₁ : Algebra.FormallyUnramified (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B))
    (h₂ : Algebra.FormallyUnramified (Localization.Away (algebraMap R A f))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f))))) :
    Algebra.FormallyUnramified A B := by
  have hB : IsLocalization.Away (algebraMap R B f)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f)))) := by
    change IsLocalization (Submonoid.powers (algebraMap R B f)) _
    rw [← algebraMapSubmonoid_powers_algebraMap (A := A) (B := B) f]
    infer_instance
  exact formallyUnramified_of_baseChange_and_awayMap (B' := (A ⊗[R] R') ⊗[A] B) f hquot h₁ h₂

/-- Étaleness descends along the two base changes of a glueing pair, given that flatness and
finite presentation do, for the canonical models of those base changes. -/
theorem etale_of_tensorRight_and_localization (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R R')))
    (hflat : Module.Flat A B) (hfp : Algebra.FinitePresentation A B)
    (h₁ : Algebra.Etale (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B))
    (h₂ : Algebra.Etale (Localization.Away (algebraMap R A f))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f))))) :
    Algebra.Etale A B := by
  have := hflat
  have := hfp
  have := h₁
  have := h₂
  have hu₁ : Algebra.FormallyUnramified (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B) := inferInstance
  have hu₂ : Algebra.FormallyUnramified (Localization.Away (algebraMap R A f))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers (algebraMap R A f)))) :=
    inferInstance
  have : Algebra.FormallyUnramified A B :=
    formallyUnramified_of_tensorRight_and_localization f hquot hu₁ hu₂
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Canonical

section EtaleRow

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type w} [CommRing B] [Algebra R B]

/-- An étale ring map is flat and of finite presentation. -/
private lemma flat_and_finitePresentation_of_etale {X Y : Type*} [CommRing X] [CommRing Y]
    {g : X →+* Y} (hg : g.Etale) : g.Flat ∧ g.FinitePresentation := by
  let _ : Algebra X Y := g.toAlgebra
  have _ : Algebra.Etale X Y := hg
  exact ⟨(inferInstance : Module.Flat X Y), (inferInstance : Algebra.FinitePresentation X Y)⟩

/-- Étaleness is stable under the base change `- ⊗[R] R'`. -/
private lemma etale_tensorMap (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Etale) :
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Etale := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Algebra.Etale A B := hφ
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  change Algebra.Etale (A ⊗[R] R') (B ⊗[R] R')
  exact Algebra.Etale.of_equiv (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl))

/-- Let `(R → R', f)` be a glueing pair and let the `R`-algebra `A` be glueable for it. A
homomorphism out of `A` is étale if and only if both its localization away from `f` and its
scalar extension to `R'` are étale. -/
theorem etale_iff_baseChange_and_awayMap_etale (f : R)
    (hglue : IsGlueingPair (algebraMap R R') f)
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact) (φ : A →ₐ[R] B) :
    φ.toRingHom.Etale ↔
      (Localization.awayMap φ.toRingHom (algebraMap R A f)).Etale ∧
        (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.Etale := by
  refine ⟨fun h => ⟨RingHom.Etale.propertyIsLocal.localizationAwayPreserves φ.toRingHom
      (algebraMap R A f) _ _ h, etale_tensorMap φ h⟩, fun h => ?_⟩
  obtain ⟨hflat, hfp⟩ := (flat_and_finitePresentation_iff_baseChange_and_awayMap f hglue hA
    φ).2 ⟨flat_and_finitePresentation_of_etale h.1, flat_and_finitePresentation_of_etale h.2⟩
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have _ : Module.Flat A B := hflat
  have _ : Algebra.FinitePresentation A B := hfp
  change Algebra.Etale A B
  let g := algebraMap R A f
  let Bₘ := Localization.Away (φ g)
  let _ : Algebra (Localization.Away g) Bₘ := (Localization.awayMap φ.toRingHom g).toAlgebra
  have _ : IsScalarTower A (Localization.Away g) Bₘ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, IsScalarTower.algebraMap_apply A B Bₘ]
    rfl
  have _ : IsLocalization.Away (algebraMap R B f) Bₘ := by
    rw [IsScalarTower.algebraMap_apply R A B]
    exact Localization.isLocalization
  have h₂ : Algebra.Etale (Localization.Away g) Bₘ := h.1
  let _ : Algebra (A ⊗[R] R') (B ⊗[R] R') :=
    (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom.toAlgebra
  have _ : Algebra.Etale (A ⊗[R] R') (B ⊗[R] R') := h.2
  have h₁ : Algebra.Etale (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] B) :=
    Algebra.Etale.of_equiv (baseChangeAlgEquiv φ (fun _ => rfl) (fun _ => rfl)).symm
  exact etale_of_baseChange_and_awayMap (B' := (A ⊗[R] R') ⊗[A] B)
    (Aₘ := Localization.Away g) (Bₘ := Bₘ) f hglue.1 hflat hfp h₁ h₂

end EtaleRow

section Fullness

/-- Let the `R`-algebra `A` be glueable for `(R → R', f)`, so that the sequence
`0 → A → (A ⊗[R] R') ⊕ (A ⊗[R] R_f) → A ⊗[R] R'_f → 0` is exact. Then `A` is the fibre product
of its two base changes over their common further base change: a pair of `R`-algebra
homomorphisms `v : C → A ⊗[R] R'` and `u : C → A ⊗[R] R_f` out of an `R`-algebra `C` whose
images agree in `A ⊗[R] R'_f` is induced by a unique `R`-algebra homomorphism `C → A`. -/
theorem exists_unique_algHom_of_isGlueableFor (f : R) (hA : IsGlueableFor (S := R') A f)
    {C : Type*} [CommRing C] [Algebra R C] (v : C →ₐ[R] A ⊗[R] R')
    (u : C →ₐ[R] A ⊗[R] Localization.Away f)
    (hcompat : ∀ c, baseChangeToAway A f (v c) = localizedBaseChangeToAway A f (u c)) :
    ∃! h : C →ₐ[R] A,
      (∀ c, (h c) ⊗ₜ[R] (1 : R') = v c) ∧
        (∀ c, (h c) ⊗ₜ[R] (1 : Localization.Away f) = u c) := by
  obtain ⟨hinj, hexact, -⟩ := hA
  have hker : ∀ c : C, tensorAwayDifference (S := R') A f (v c, u c) = 0 := fun c => by
    rw [tensorAwayDifference_apply]
    exact sub_eq_zero_of_eq (hcompat c)
  choose g hg using fun c : C => (hexact (v c, u c)).mp (hker c)
  have hg' : ∀ c : C, g c ⊗ₜ[R] (1 : R') = v c ∧
      g c ⊗ₜ[R] (1 : Localization.Away f) = u c := fun c => by
    simpa only [toTensorBaseChanges_apply, Prod.mk.injEq] using hg c
  have hg1 : ∀ c : C, g c ⊗ₜ[R] (1 : R') = v c := fun c => (hg' c).1
  have hg2 : ∀ c : C, g c ⊗ₜ[R] (1 : Localization.Away f) = u c := fun c => (hg' c).2
  have hT : ∀ a b : A, a ⊗ₜ[R] (1 : R') = b ⊗ₜ[R] (1 : R') →
      a ⊗ₜ[R] (1 : Localization.Away f) = b ⊗ₜ[R] (1 : Localization.Away f) → a = b :=
    fun a b h₁ h₂ => hinj (by
      rw [toTensorBaseChanges_apply, toTensorBaseChanges_apply, h₁, h₂])
  have hone : g 1 = 1 :=
    hT _ _ (by rw [hg1, map_one, Algebra.TensorProduct.one_def])
      (by rw [hg2, map_one, Algebra.TensorProduct.one_def])
  have hzero : g 0 = 0 :=
    hT _ _ (by rw [hg1, map_zero, TensorProduct.zero_tmul])
      (by rw [hg2, map_zero, TensorProduct.zero_tmul])
  have hmul : ∀ c₁ c₂ : C, g (c₁ * c₂) = g c₁ * g c₂ := fun c₁ c₂ =>
    hT _ _
      (by rw [hg1, map_mul, ← hg1 c₁, ← hg1 c₂, Algebra.TensorProduct.tmul_mul_tmul, mul_one])
      (by rw [hg2, map_mul, ← hg2 c₁, ← hg2 c₂, Algebra.TensorProduct.tmul_mul_tmul, mul_one])
  have hadd : ∀ c₁ c₂ : C, g (c₁ + c₂) = g c₁ + g c₂ := fun c₁ c₂ =>
    hT _ _ (by rw [hg1, map_add, ← hg1 c₁, ← hg1 c₂, TensorProduct.add_tmul])
      (by rw [hg2, map_add, ← hg2 c₁, ← hg2 c₂, TensorProduct.add_tmul])
  have hcomm : ∀ r : R, g (algebraMap R C r) = algebraMap R A r := fun r =>
    hT _ _ (by rw [hg1, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply])
      (by rw [hg2, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply])
  refine ⟨{ toFun := g
            map_one' := hone
            map_mul' := hmul
            map_zero' := hzero
            map_add' := hadd
            commutes' := hcomm }, ⟨hg1, hg2⟩, ?_⟩
  intro ψ hψ
  ext c
  change ψ c = g c
  exact hT _ _ (by rw [hψ.1 c, hg1 c]) (by rw [hψ.2 c, hg2 c])

end Fullness

end BeauvilleLaszlo

end
