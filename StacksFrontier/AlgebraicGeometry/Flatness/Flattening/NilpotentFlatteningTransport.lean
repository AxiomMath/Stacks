module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatStratificationChain
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFPBase
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP

/-!
# Transports needed by the induction of the proof of Stacks 05U9

The induction on the length of a generic flatness stratification in the proof of Stacks 05U9
applies the proposition over quotients of the base and reads the result back. Three changes of
presentation are needed on the way, and they are collected here so that the induction itself
reads as the source's argument.

* `Stacks.FlatStratification.ofLinearEquiv` moves a stratification along a linear equivalence of
  the module. The induction hands the stratification of `N ⧸ EN` to a situation whose module is
  the *same* quotient presented as `N ⧸ (EB) N`, and those two descriptions are related by
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientNEquiv`.

* `Stacks.flat_quotient_map_of_flat_quotient_sup` turns flatness modulo `E ⊔ C` over `A` into
  flatness modulo the extension of `C` over `A ⧸ E`. This is how "by induction on `t` again, we
  also have flatness modulo the powers of `J`" reaches the hypothesis `hpow` of
  `Stacks.flat_of_least_flattening_of_flat_away`, which asks for it over the base `A ⧸ J₀` the
  index `i = 0` has been reduced to.

* `Stacks.flat_tensorQuotient_of_flat_away_of_le` reads the flatness clause of a stratification
  on away localizations of `A ⧸ E` itself, rather than of `(A ⧸ E) ⧸ K(A ⧸ E)` as
  `Stacks.flat_tensorQuotient_of_flat_away` does. The two agree exactly when `K ≤ E`, which is
  the case at the index the henselization core is applied to, `K` being `K₀` and `E` the closure
  ideal `J₀ ⊇ K₀`; and only this form is the hypothesis `hU` of
  `Stacks.flat_of_least_flattening_of_flat_away`.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Stacks

namespace FlatStratification

variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N] {t : ℕ}

/-- **A generic flatness stratification transported along a linear equivalence of the module.**
Only the flatness clause mentions the module, and it is a statement about the base changes
`L ⊗_A N`, which an `A`-linear equivalence `N ≃ N'` carries across. -/
def ofLinearEquiv (S : FlatStratification A N t) {N' : Type w} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') : FlatStratification A N' t where
  ideal := S.ideal
  base_le_nilradical := S.base_le_nilradical
  fg := S.fg
  le_succ := S.le_succ
  eq_top := S.eq_top
  flat_away i a ha L _ _ _ _ _ := by
    let := S.flat_away i a ha L
    exact Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) e.symm)

/-- The ideals of a flatness stratification transported along a linear equivalence are the
ideals of the original stratification. -/
@[simp]
theorem ofLinearEquiv_ideal (S : FlatStratification A N t) {N' : Type w} [AddCommGroup N']
    [Module A N'] (e : N ≃ₗ[A] N') : (S.ofLinearEquiv e).ideal = S.ideal :=
  rfl

end FlatStratification

/-- **Flatness modulo an extended ideal, from flatness modulo the sum.** If `N ⧸ (E ⊔ C)N` is
flat over `A ⧸ (E ⊔ C)`, then the reduction of `N ⧸ EN` modulo the extension of `C` to `A ⧸ E` is
flat over `(A ⧸ E) ⧸ C(A ⧸ E)`.

The two sides describe the same ring and the same module: `(A ⧸ E) ⧸ C(A ⧸ E)` is `A ⧸ (E ⊔ C)`
by `DoubleQuot.quotQuotEquivQuotSup`, and the iterated quotient of the module is
`N ⧸ (E ⊔ C)N` by `Submodule.quotientQuotientEquivQuotient`. -/
theorem flat_quotient_map_of_flat_quotient_sup {A : Type u} [CommRing A] {N : Type v}
    [AddCommGroup N] [Module A N] (E C : Ideal A)
    (h : Module.Flat (A ⧸ (E ⊔ C)) (N ⧸ ((E ⊔ C) • (⊤ : Submodule A N)))) :
    Module.Flat ((A ⧸ E) ⧸ C.map (Ideal.Quotient.mk E))
      ((N ⧸ (E • (⊤ : Submodule A N))) ⧸
        (C.map (Ideal.Quotient.mk E) •
          (⊤ : Submodule (A ⧸ E) (N ⧸ (E • (⊤ : Submodule A N)))))) := by
  have := h
  set P := N ⧸ (E • (⊤ : Submodule A N)) with hP
  have hle : (E • (⊤ : Submodule A N)) ≤ (E ⊔ C) • (⊤ : Submodule A N) :=
    Submodule.smul_mono_left le_sup_left
  have hbot : (E • (⊤ : Submodule A N)).map (E • (⊤ : Submodule A N)).mkQ = ⊥ :=
    le_antisymm (Submodule.map_le_iff_le_comap.mpr
      (by rw [Submodule.comap_bot, Submodule.ker_mkQ])) bot_le
  have hset : ((C.map (Ideal.Quotient.mk E) • ⊤ : Submodule (A ⧸ E) P) : Set P) =
      ((((E ⊔ C) • (⊤ : Submodule A N)).map (E • (⊤ : Submodule A N)).mkQ :
        Submodule A P) : Set P) := by
    rw [← Ideal.Quotient.algebraMap_eq E,
      Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := A) (A := A ⧸ E)
      (M := P) C]
    congr 1
    rw [Submodule.sup_smul, Submodule.map_sup, hbot, bot_sup_eq, Submodule.map_smul'',
      Submodule.map_top, Submodule.range_mkQ]
  refine Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
    (R₂ := A ⧸ (E ⊔ C)) (Y := N ⧸ ((E ⊔ C) • (⊤ : Submodule A N)))
    (DoubleQuot.quotQuotEquivQuotSup E C)
    ((Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _ hset).trans
      (Submodule.quotientQuotientEquivQuotient _ _ hle).toAddEquiv) ?_
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ n
  rfl

/-- **The flatness clause of a stratification on away localizations of the quotient itself.**
Let `K ≤ E` be ideals of `A` and let `a : A`. If `N` is flat over every localization of `A ⧸ K`
away from the image of `a`, then `N ⧸ EN` is flat over every localization of `A ⧸ E` away from
the image of `a`.

`Stacks.flat_tensorQuotient_of_flat_away` reads the clause on localizations of
`(A ⧸ E) ⧸ K(A ⧸ E)`; when `K ≤ E` that ring is `A ⧸ E` itself, and this is the form the
hypothesis `hU` of `Stacks.flat_of_least_flattening_of_flat_away` takes. -/
theorem flat_tensorQuotient_of_flat_away_of_le {A : Type u} [CommRing A] {N : Type v}
    [AddCommGroup N] [Module A N] (E K : Ideal A) (hKE : K ≤ E) (a : A)
    (hK : ∀ (L₀ : Type u) [CommRing L₀] [Algebra A L₀] [Algebra (A ⧸ K) L₀]
      [IsScalarTower A (A ⧸ K) L₀] [IsLocalization.Away (Ideal.Quotient.mk K a) L₀],
      Module.Flat L₀ (L₀ ⊗[A] N))
    (L : Type u) [CommRing L] [Algebra (A ⧸ E) L]
    [IsLocalization.Away (Ideal.Quotient.mk E a) L] :
    Module.Flat L (L ⊗[A ⧸ E] (N ⧸ (E • (⊤ : Submodule A N)))) := by
  let : Algebra A L := ((algebraMap (A ⧸ E) L).comp (algebraMap A (A ⧸ E))).toAlgebra
  have : IsScalarTower A (A ⧸ E) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hkill : ∀ x ∈ K, algebraMap A L x = 0 := by
    intro x hx
    calc algebraMap A L x = algebraMap (A ⧸ E) L (Ideal.Quotient.mk E x) := rfl
      _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hKE hx), map_zero]
  let : Algebra (A ⧸ K) L := (Ideal.Quotient.lift K (algebraMap A L) hkill).toAlgebra
  have : IsScalarTower A (A ⧸ K) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : IsUnit (algebraMap (A ⧸ K) L (Ideal.Quotient.mk K a)) := by
    have h4 : algebraMap (A ⧸ K) L (Ideal.Quotient.mk K a) =
        algebraMap (A ⧸ E) L (Ideal.Quotient.mk E a) := rfl
    rw [h4]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact AlgebraicGeometry.flat_tensorQuotient_of_flat_tensor E N
    (flat_tensor_of_localization_away K a (Localization.Away (Ideal.Quotient.mk K a)) L hunit
      (hK (Localization.Away (Ideal.Quotient.mk K a))))

/-- Flatness of a base change along a linear equivalence of the module. -/
theorem flat_tensor_of_linearEquiv {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N]
    [Module A N] {N' : Type w} [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N')
    (L : Type*) [CommRing L] [Algebra A L] (h : Module.Flat L (L ⊗[A] N)) :
    Module.Flat L (L ⊗[A] N') := by
  have := h
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) e.symm)

/-- Flatness of a reduction `N ⧸ DN` over `A ⧸ D` along a linear equivalence of `N`. An
`A`-linear equivalence carries `DN` onto `DN'`, so it descends to the reductions, and the
descended map is `A ⧸ D`-linear because `A → A ⧸ D` is surjective. -/
theorem flat_quotient_smul_top_of_linearEquiv {A : Type u} [CommRing A] {N : Type v}
    [AddCommGroup N] [Module A N] {N' : Type w} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (D : Ideal A)
    (h : Module.Flat (A ⧸ D) (N ⧸ (D • (⊤ : Submodule A N)))) :
    Module.Flat (A ⧸ D) (N' ⧸ (D • (⊤ : Submodule A N'))) := by
  have := h
  have hmap : (D • (⊤ : Submodule A N)).map (e : N →ₗ[A] N') = D • (⊤ : Submodule A N') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact Module.Flat.of_linearEquiv
    ((Submodule.Quotient.equiv (D • (⊤ : Submodule A N)) (D • (⊤ : Submodule A N')) e
      hmap).extendScalarsOfSurjective
        (S := A ⧸ D) Ideal.Quotient.mk_surjective).symm

end Stacks

end
