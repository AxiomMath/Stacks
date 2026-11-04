module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.DeterminantBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Transport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tame symbol under a flat local homomorphism with `𝔪 A' = 𝔪'`

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of Noetherian local rings of
dimension one with `𝔪 A' = 𝔪'`. This is the case `m = length_{A'}(A' / 𝔪 A') = 1` of
Stacks 0EPG; no hypothesis is placed on the residue field extension `κ → κ'`. For nonzerodivisors
`a, b ∈ A`, whose images are nonzerodivisors of `A'` by flatness, the symbol of Stacks 02PZ
satisfies

`κ → κ'` carries `d_A(a, b)` to `d_{A'}(a, b)`,

and consequently the tame symbol `∂_A` on `Q(A)^*` of `Stacks.Chow.tameSymbolOfKrullDimOne` is
carried to `∂_{A'}` on `Q(A')^*` along the induced map `Q(A) → Q(A')`.

The symbol `d_A(a, b)` is the periodic determinant of the complex on `A / abA` with
differentials multiplication by `a` and by `b`, and `d_{A'}(a, b)` that of the complex on
`A' / abA'`. The map `A / abA → A' / abA'` intertwines the differentials and its image generates
`A' / abA'`. The images of the two differentials have lengths `length_A(A/bA)` and
`length_A(A/aA)`, respectively `length_{A'}(A'/bA')` and `length_{A'}(A'/aA')`, and these agree
because the order of vanishing is multiplied by `length_{A'}(A'/𝔪A') = 1` (Stacks 02M1). So
`Stacks.Chow.map_periodicDeterminant_of_map` applies.

## Main definitions

* `Stacks.Chow.quotientLsmulMap` — the map `A / abA → A' / abA'`.

## Main results

* `Stacks.Chow.length_range_periodicQuotientPhi`, `Stacks.Chow.length_range_periodicQuotientPsi`
  — the lengths of the two images in the periodic complex on `M / φψM`.
* `Stacks.Chow.map_moduleSymbol_of_flat`, `Stacks.Chow.map_regularModuleSymbol_of_flat` —
  Stacks 0EPG for `m = 1`, on nonzerodivisors.
* `Stacks.Chow.map_tameSymbolOfKrullDimOne_of_flat` — Stacks 0EPG for `m = 1`, on the total
  rings of fractions.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
-/

@[expose] public section

noncomputable section

open IsLocalRing Module.FiniteLength AlgebraicGeometry

universe u v w w'

namespace Stacks.Chow

section PeriodicQuotientLength

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The image of the map induced by `φ` on `M / φψM` has the length of `M / ψM`: its kernel is
the image `ψM / φψM` of the map induced by `ψ`. -/
theorem length_range_periodicQuotientPhi (φ ψ : M →ₗ[R] M) (hφ : Function.Injective φ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    Module.length R (LinearMap.range (periodicQuotientPhi φ ψ hcomm)) =
      Module.length R (M ⧸ LinearMap.range ψ) := by
  have hker : LinearMap.ker (periodicQuotientPhi φ ψ hcomm) =
      (LinearMap.range ψ).map (LinearMap.range (φ ∘ₗ ψ)).mkQ := by
    rw [(exact_periodicQuotient_psi_phi φ ψ hφ hcomm).linearMap_ker_eq,
      ← LinearMap.range_comp_of_range_eq_top (periodicQuotientPsi φ ψ hcomm)
        (Submodule.range_mkQ _),
      periodicQuotientPsi, Submodule.mapQ_mkQ]
    exact LinearMap.range_comp _ _
  have hle : LinearMap.range (φ ∘ₗ ψ) ≤ LinearMap.range ψ := by
    rw [hcomm]
    exact LinearMap.range_comp_le_range φ ψ
  rw [← (periodicQuotientPhi φ ψ hcomm).quotKerEquivRange.length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq,
    (Submodule.quotientQuotientEquivQuotient _ _ hle).length_eq]

/-- The image of the map induced by `ψ` on `M / φψM` has the length of `M / φM`. -/
theorem length_range_periodicQuotientPsi (φ ψ : M →ₗ[R] M) (hψ : Function.Injective ψ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    Module.length R (LinearMap.range (periodicQuotientPsi φ ψ hcomm)) =
      Module.length R (M ⧸ LinearMap.range φ) := by
  have hker : LinearMap.ker (periodicQuotientPsi φ ψ hcomm) =
      (LinearMap.range φ).map (LinearMap.range (φ ∘ₗ ψ)).mkQ := by
    rw [(exact_periodicQuotient_phi_psi φ ψ hψ hcomm).linearMap_ker_eq,
      ← LinearMap.range_comp_of_range_eq_top (periodicQuotientPhi φ ψ hcomm)
        (Submodule.range_mkQ _),
      periodicQuotientPhi, Submodule.mapQ_mkQ]
    exact LinearMap.range_comp _ _
  have hle : LinearMap.range (φ ∘ₗ ψ) ≤ LinearMap.range φ :=
    LinearMap.range_comp_le_range ψ φ
  rw [← (periodicQuotientPsi φ ψ hcomm).quotKerEquivRange.length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq,
    (Submodule.quotientQuotientEquivQuotient _ _ hle).length_eq]

end PeriodicQuotientLength

section QuotientMap

variable {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']

/-- The map `A / abA → A' / abA'` induced by `A → A'`. -/
def quotientLsmulMap (a b : A) :
    (A ⧸ LinearMap.range (LinearMap.lsmul A A a ∘ₗ LinearMap.lsmul A A b)) →ₗ[A]
      (A' ⧸ LinearMap.range (LinearMap.lsmul A' A' (algebraMap A A' a) ∘ₗ
        LinearMap.lsmul A' A' (algebraMap A A' b))) :=
  Submodule.liftQ _ (((Submodule.mkQ _).restrictScalars A) ∘ₗ Algebra.linearMap A A') (by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨algebraMap A A' w, by simp⟩)

/-- `quotientLsmulMap` sends the class of `w ∈ A` to the class of its image in `A'`. -/
@[simp]
theorem quotientLsmulMap_mk (a b w : A) :
    quotientLsmulMap (A' := A') a b (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (algebraMap A A' w) :=
  rfl

/-- The image of `A / abA` generates `A' / abA'` over `A'`. -/
theorem span_range_quotientLsmulMap (a b : A) :
    Submodule.span A' (Set.range (quotientLsmulMap (A' := A') a b)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using Submodule.Quotient.induction_on with
  | _ w =>
    have hz : (Submodule.Quotient.mk w : A' ⧸ LinearMap.range
        (LinearMap.lsmul A' A' (algebraMap A A' a) ∘ₗ
          LinearMap.lsmul A' A' (algebraMap A A' b))) =
        w • quotientLsmulMap (A' := A') a b (Submodule.Quotient.mk 1) := by
      rw [quotientLsmulMap_mk, map_one, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
    rw [hz]
    exact Submodule.smul_mem _ w (Submodule.subset_span ⟨_, rfl⟩)

/-- `quotientLsmulMap` intertwines multiplication by `a` on `A / abA` with multiplication by the
image of `a` on `A' / abA'`. -/
theorem quotientLsmulMap_phi (a b : A) (n : A ⧸ LinearMap.range
    (LinearMap.lsmul A A a ∘ₗ LinearMap.lsmul A A b)) :
    quotientLsmulMap (A' := A') a b
        (periodicQuotientPhi (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
          (range_lsmul_comp_eq a b) n) =
      periodicQuotientPhi (LinearMap.lsmul A' A' (algebraMap A A' a))
        (LinearMap.lsmul A' A' (algebraMap A A' b)) (range_lsmul_comp_eq _ _)
        (quotientLsmulMap (A' := A') a b n) := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ n
  rw [Submodule.mkQ_apply, periodicQuotientPhi, Submodule.mapQ_apply, quotientLsmulMap_mk,
    quotientLsmulMap_mk, periodicQuotientPhi, Submodule.mapQ_apply]
  congr 1
  simp

/-- `quotientLsmulMap` intertwines multiplication by `b` on `A / abA` with multiplication by the
image of `b` on `A' / abA'`. -/
theorem quotientLsmulMap_psi (a b : A) (n : A ⧸ LinearMap.range
    (LinearMap.lsmul A A a ∘ₗ LinearMap.lsmul A A b)) :
    quotientLsmulMap (A' := A') a b
        (periodicQuotientPsi (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
          (range_lsmul_comp_eq a b) n) =
      periodicQuotientPsi (LinearMap.lsmul A' A' (algebraMap A A' a))
        (LinearMap.lsmul A' A' (algebraMap A A' b)) (range_lsmul_comp_eq _ _)
        (quotientLsmulMap (A' := A') a b n) := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ n
  rw [Submodule.mkQ_apply, periodicQuotientPsi, Submodule.mapQ_apply, quotientLsmulMap_mk,
    quotientLsmulMap_mk, periodicQuotientPsi, Submodule.mapQ_apply]
  congr 1
  simp

end QuotientMap

section FlatBaseChange

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {A' : Type v} [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A']
  [Algebra A A'] [Module.Flat A A'] [IsLocalHom (algebraMap A A')]

omit [IsNoetherianRing A] [IsNoetherianRing A'] [Module.Flat A A'] [IsLocalHom (algebraMap A A')] in
/-- If `𝔪 A' = 𝔪'`, then `length_{A'}(A' / 𝔪 A') = 1`. -/
theorem length_quotient_extendedMaximalIdeal_eq_one
    (hmax : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A') :
    Module.length A' (A' ⧸ extendedMaximalIdeal A A') = 1 := by
  rw [extendedMaximalIdeal, hmax]
  exact Module.length_eq_one_iff.mpr
    (isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal A').out)

/-- The symbol of Stacks 02PZ of `A` as a module over itself, on two nonzerodivisors, is carried
by the residue field map to the symbol of `A'` on their images, when `𝔪 A' = 𝔪'`. -/
theorem map_moduleSymbol_of_flat
    (hmax : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A')
    (hdim : ringKrullDim A = 1) (a b : nonZeroDivisors A)
    (ha : IsSMulRegular A (a : A)) (hb : IsSMulRegular A (b : A))
    (ha' : IsSMulRegular A' (algebraMap A A' a)) (hb' : IsSMulRegular A' (algebraMap A A' b))
    (hd : Module.supportDim A A = 1) (hd' : Module.supportDim A' A' = 1) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (moduleSymbol (M := A) (a : A) (b : A) ha hb hd) =
      moduleSymbol (M := A') (algebraMap A A' a) (algebraMap A A' b) ha' hb' hd' := by
  have := krullDimLE_one_of_ringKrullDim_eq_one hdim
  have hord (x : nonZeroDivisors A) :
      moduleLength A' (A' ⧸ LinearMap.range (LinearMap.lsmul A' A' (algebraMap A A' x))) =
        moduleLength A (A ⧸ LinearMap.range (LinearMap.lsmul A A (x : A))) := by
    rw [moduleLength_quotient_range_lsmul, moduleLength_quotient_range_lsmul,
      ord_toNat_algebraMap_eq_ord_toNat_mul
        (length_quotient_extendedMaximalIdeal_eq_one hmax) x.2, mul_one]
  rw [moduleSymbol_eq_symbolOfPeriodicMaps, moduleSymbol_eq_symbolOfPeriodicMaps]
  unfold symbolOfPeriodicMaps
  exact map_periodicDeterminant_of_map hmax.ge _ _ _ _ _ _ _ _ _ _
    (quotientLsmulMap (A' := A') (a : A) (b : A)) (span_range_quotientLsmulMap _ _)
    (quotientLsmulMap_phi _ _) (quotientLsmulMap_psi _ _)
    (by
      rw [moduleLength, moduleLength,
        length_range_periodicQuotientPhi (LinearMap.lsmul A' A' (algebraMap A A' a))
          (LinearMap.lsmul A' A' (algebraMap A A' b)) ha',
        length_range_periodicQuotientPhi (LinearMap.lsmul A A (a : A))
          (LinearMap.lsmul A A (b : A)) ha]
      exact hord b)
    (by
      rw [moduleLength, moduleLength,
        length_range_periodicQuotientPsi (LinearMap.lsmul A' A' (algebraMap A A' a))
          (LinearMap.lsmul A' A' (algebraMap A A' b)) hb',
        length_range_periodicQuotientPsi (LinearMap.lsmul A A (a : A))
          (LinearMap.lsmul A A (b : A)) hb]
      exact hord a)

/-- **Stacks 0EPG with `m = 1`, on nonzerodivisors.** Let `A → A'` be a flat local homomorphism
of Noetherian local rings of dimension one with `𝔪 A' = 𝔪'`. For nonzerodivisors `a, b` of `A`,
the induced map of residue fields carries the symbol `d_A(a, b)` of Stacks 02PZ to
`d_{A'}(a, b)`. No hypothesis is placed on the residue field extension. -/
theorem map_regularModuleSymbol_of_flat
    (hmax : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A')
    (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1) (a b : nonZeroDivisors A) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom (regularModuleSymbol hdim a b) =
      regularModuleSymbol hdim' (flatNonZeroDivisor A' a) (flatNonZeroDivisor A' b) :=
  map_moduleSymbol_of_flat hmax hdim a b _ _
    (isRegular_iff_mem_nonZeroDivisors.mpr (flatNonZeroDivisor A' a).2).isSMulRegular
    (isRegular_iff_mem_nonZeroDivisors.mpr (flatNonZeroDivisor A' b).2).isSMulRegular _
    ((Module.supportDim_self_eq_ringKrullDim A').trans hdim')

omit [IsNoetherianRing A] [IsLocalRing A] [IsNoetherianRing A'] [IsLocalRing A']
  [IsLocalHom (algebraMap A A')] in
/-- A flat ring map carries the nonzerodivisors into the nonzerodivisors. -/
@[ega "0 6.3.4" "special case", sga "1 IV 1.3" "special case"]
theorem nonZeroDivisors_le_comap_of_flat :
    nonZeroDivisors A ≤ (nonZeroDivisors A').comap (algebraMap A A') :=
  fun _ ha ↦ algebraMap_mem_nonZeroDivisors_of_flat ha

variable (Q : Type w) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
  (Q' : Type w') [CommRing Q'] [Algebra A' Q'] [IsFractionRing A' Q']

omit [IsNoetherianRing A] [IsLocalRing A] [IsNoetherianRing A'] [IsLocalRing A']
  [IsLocalHom (algebraMap A A')] in
/-- The map of total rings of fractions carries the class of a nonzerodivisor to the class of
its image. -/
theorem units_map_regularFractionUnit_of_flat (a : nonZeroDivisors A) :
    Units.map (IsLocalization.map Q' (algebraMap A A') (nonZeroDivisors_le_comap_of_flat (A := A)
        (A' := A')) : Q →+* Q').toMonoidHom (regularFractionUnit (Q := Q) a) =
      regularFractionUnit (Q := Q') (flatNonZeroDivisor A' a) :=
  Units.ext (by simp [IsLocalization.map_eq])

/-- **Stacks 0EPG with `m = 1`, on the total rings of fractions.** Let `A → A'` be a flat local
homomorphism of Noetherian local rings of dimension one with `𝔪 A' = 𝔪'`, with total rings of
fractions `Q` and `Q'`. For units `f, g` of `Q`, the induced map of residue fields carries
`∂_A(f, g)` to `∂_{A'}(f, g)`, where `f` and `g` are viewed in `Q'` through the induced map
`Q → Q'`. -/
theorem map_tameSymbolOfKrullDimOne_of_flat
    (hmax : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A')
    (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1) (f g : Qˣ) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (tameSymbolOfKrullDimOne hdim Q f g) =
      tameSymbolOfKrullDimOne hdim' Q'
        (Units.map (IsLocalization.map Q' (algebraMap A A')
          (nonZeroDivisors_le_comap_of_flat (A := A) (A' := A')) : Q →+* Q').toMonoidHom f)
        (Units.map (IsLocalization.map Q' (algebraMap A A')
          (nonZeroDivisors_le_comap_of_flat (A := A) (A' := A')) : Q →+* Q').toMonoidHom g) := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) g
  subst hf hg
  simp only [map_mul, map_inv, units_map_regularFractionUnit_of_flat, TameSymbol.map_mul_left,
    TameSymbol.inv_left, TameSymbol.map_mul_right, TameSymbol.inv_right,
    tameSymbolOfKrullDimOne_regularFractionUnit, map_regularModuleSymbol_of_flat hmax hdim hdim']

end FlatBaseChange

end Stacks.Chow

end
