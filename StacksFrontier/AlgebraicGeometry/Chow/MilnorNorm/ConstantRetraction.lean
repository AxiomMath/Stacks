module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.AffineLineResidue

/-!
# The constants are a direct summand of the Milnor K-theory of a rational function field

Let `k` be a field and let `F` be the field of rational functions over `k`, realized as the
fraction field of `k[X]`. The inclusion of the constants induces

`res : K^M_n(k) ⟶ K^M_n(F)`

in every degree, and this file shows that `res` is **split injective**: the tame symbol at the
origin of `A¹_k`, applied after multiplying by the symbol of the uniformizer `X`, is a retraction
of it.

The local ring `A` of `A¹_k` at the origin is a discrete valuation ring with uniformizer `X` and
residue field `k` (`Stacks.Chow.residueFieldAtOriginEquiv`), the constants are units of `A` whose
residues are themselves, and `Stacks.Chow.dvrMilnorTameSymbol_uniformizer` evaluates the tame
symbol on a symbol of units of `A` multiplied by the uniformizer:

`∂_A {c_1, …, c_n, X} = {c_1, …, c_n}`.

Since the symbol products generate the Milnor K-groups
(`coe_mem_of_forall_milnorKSymbolProd_mem`), that computation on symbols is enough.

This is the first half of the exactness of Milnor's sequence for a rational function field,

`0 ⟶ K^M_n(k) ⟶ K^M_n(F) ⟶ ⨁_P K^M_{n-1}(k[X]/P) ⟶ 0`,

whose remaining content — that the residues of
`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.AffineLineResidue` are jointly surjective, and
that their joint kernel is exactly the constants — is not proved here.

## Main definitions

* `milnorKMulSymbol` — multiplication by a degree-one symbol, `K^M_n(k) ⟶ K^M_{n+1}(k)`.
* `Stacks.Chow.localRingAtOrigin` — the local ring of `A¹_k` at the origin.
* `Stacks.Chow.residueOfConstants`, `Stacks.Chow.residueFieldAtOriginEquiv` — the residue field
  at the origin is `k`.
* `Stacks.Chow.constantsHom`, `Stacks.Chow.constantInclusion` — the constants, and the induced
  map of Milnor K-groups.
* `Stacks.Chow.constantRetraction` — the retraction.

## Main results

* `milnorKRingMap_milnorKSymbol`, `milnorKRingMap_milnorKSymbolProd` — symbols are natural in the
  field.
* `Stacks.Chow.irreducible_algebraMap_X` — `X` is a uniformizer at the origin.
* `Stacks.Chow.constantRetraction_constantInclusion` — the retraction is one.
* `Stacks.Chow.constantInclusion_injective` — **`K^M_n(k) ⟶ K^M_n(F)` is injective.**

## Implementation notes

The retraction is built from the tame symbol at the specific uniformizer `X`, that is from
`Stacks.Chow.dvrMilnorTameSymbol`, rather than from
`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.AffineLineResidue`'s
`Stacks.Chow.affineLineResidue`, which chooses its own uniformizer. Identifying the two would
need the independence of the tame symbol from the uniformizer, which is not proved in this
development. Nothing below depends on that: a retraction built from any additive map proves the
injectivity of the inclusion just as well.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

/-! ### Symbols are natural in the field -/

section Symbols

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂]

/-- The symbol of a unit is natural in the field. -/
theorem milnorKRingMap_milnorKSymbol (φ : k₁ →+* k₂) (u : k₁ˣ) :
    milnorKRingMap φ (milnorKSymbol k₁ u) = milnorKSymbol k₂ (Units.map (φ : k₁ →* k₂) u) := by
  rw [milnorKSymbol_eq_mk', milnorKRingMap_mk', milnorKTensorMap_ι, milnorKUnitsMap_ofMul,
    milnorKSymbol_eq_mk']

/-- A symbol product is natural in the field. -/
theorem milnorKRingMap_milnorKSymbolProd (φ : k₁ →+* k₂) (l : List k₁ˣ) :
    milnorKRingMap φ (milnorKSymbolProd k₁ l) =
      milnorKSymbolProd k₂ (l.map (Units.map (φ : k₁ →* k₂))) := by
  induction l with
  | nil => simpa only [milnorKSymbolProd_nil, List.map_nil] using map_one (milnorKRingMap φ)
  | cons u l ih =>
      rw [milnorKSymbolProd_cons, map_mul, milnorKRingMap_milnorKSymbol, ih, List.map_cons,
        milnorKSymbolProd_cons]

end Symbols

/-! ### Multiplication by a degree-one symbol -/

/-- Multiplication by the symbol `{u}`, as a map `K^M_n(k) ⟶ K^M_{n+1}(k)`. -/
def milnorKMulSymbol (k : Type u) [Field k] (n : ℕ) (u : kˣ) :
    MilnorKTheory k n →+ MilnorKTheory k (n + 1) where
  toFun β := ⟨(β : MilnorKRing k) * milnorKSymbol k u,
    SetLike.mul_mem_graded β.2 (milnorKSymbol_mem_milnorKGrading u)⟩
  map_zero' := Subtype.ext (zero_mul _)
  map_add' _ _ := Subtype.ext (add_mul _ _ _)

/-- `milnorKMulSymbol k n u β` is the product `β * {u}` in the Milnor K-ring. -/
@[simp]
theorem coe_milnorKMulSymbol {k : Type u} [Field k] (n : ℕ) (u : kˣ)
    (β : MilnorKTheory k n) :
    (milnorKMulSymbol k n u β : MilnorKRing k) = (β : MilnorKRing k) * milnorKSymbol k u :=
  rfl

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-! ### The local ring at the origin -/

/-- The origin is a closed point of `A¹_k`. -/
instance isMaximal_span_singleton_X : (Ideal.span {(X : Polynomial k)}).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial irreducible_X

/-- The local ring of `A¹_k` at the origin. -/
abbrev localRingAtOrigin (k : Type u) [Field k] : Type u :=
  Localization.AtPrime (Ideal.span {(X : Polynomial k)})

/-- The local ring of `A¹_k` at the origin is a discrete valuation ring. -/
instance isDiscreteValuationRing_localRingAtOrigin :
    IsDiscreteValuationRing (localRingAtOrigin k) :=
  isDiscreteValuationRing_localizationAtPrime_polynomial _

/-- **`X` is a uniformizer of the local ring of `A¹_k` at the origin.** The case `p = X` of
`Stacks.Chow.irreducible_algebraMap_self`. -/
theorem irreducible_algebraMap_X :
    Irreducible (algebraMap (Polynomial k) (localRingAtOrigin k) (X : Polynomial k)) :=
  irreducible_algebraMap_self

/-- The image of the uniformizer `X` lies in the maximal ideal. -/
theorem algebraMap_X_mem_maximalIdeal :
    algebraMap (Polynomial k) (localRingAtOrigin k) (X : Polynomial k) ∈
      maximalIdeal (localRingAtOrigin k) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self (X : Polynomial k))

/-! ### The residue field at the origin is `k` -/

/-- A constant, read in the residue field of the local ring of `A¹_k` at the origin. -/
def residueOfConstants (k : Type u) [Field k] : k →+* ResidueField (localRingAtOrigin k) :=
  (residue (localRingAtOrigin k)).comp
    ((algebraMap (Polynomial k) (localRingAtOrigin k)).comp (C : k →+* Polynomial k))

/-- The residue of a polynomial at the origin is its constant term. -/
theorem residue_algebraMap_polynomial (f : Polynomial k) :
    residue (localRingAtOrigin k) (algebraMap (Polynomial k) (localRingAtOrigin k) f) =
      residueOfConstants k (f.coeff 0) := by
  have hf : algebraMap (Polynomial k) (localRingAtOrigin k) f =
      algebraMap (Polynomial k) (localRingAtOrigin k) (C (f.coeff 0)) +
        algebraMap (Polynomial k) (localRingAtOrigin k) (X : Polynomial k) *
          algebraMap (Polynomial k) (localRingAtOrigin k) (divX f) := by
    rw [← map_mul, ← map_add]
    exact congrArg _ (by rw [add_comm]; exact (X_mul_divX_add f).symm)
  rw [hf, map_add, map_mul,
    (IsLocalRing.residue_eq_zero_iff _).mpr algebraMap_X_mem_maximalIdeal, zero_mul, add_zero]
  rfl

/-- The constants exhaust the residue field at the origin. -/
theorem residueOfConstants_bijective : Function.Bijective (residueOfConstants k) := by
  refine ⟨(residueOfConstants k).injective, fun y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨f, g⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Ideal.span {(X : Polynomial k)}).primeCompl a
  have hg0 : (g : Polynomial k).coeff 0 ≠ 0 := fun h ↦
    g.2 (Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr h))
  have hne : residueOfConstants k ((g : Polynomial k).coeff 0) ≠ 0 := fun h ↦
    hg0 ((residueOfConstants k).injective (by rw [h, map_zero]))
  refine ⟨f.coeff 0 / (g : Polynomial k).coeff 0, ?_⟩
  have h := congrArg (residue (localRingAtOrigin k))
    (IsLocalization.mk'_spec (localRingAtOrigin k) f g)
  rw [map_mul, residue_algebraMap_polynomial, residue_algebraMap_polynomial] at h
  rw [map_div₀, ← h, mul_div_assoc, div_self hne, mul_one]

/-- **The residue field of `A¹_k` at the origin is `k`.** -/
def residueFieldAtOriginEquiv (k : Type u) [Field k] : k ≃+* ResidueField (localRingAtOrigin k) :=
  RingEquiv.ofBijective (residueOfConstants k) residueOfConstants_bijective

/-! ### The constants in the field of rational functions -/

/-- A constant, as an element of the field of rational functions. -/
def constantsHom (k : Type u) [Field k] : k →+* RatFunc k :=
  (algebraMap (Polynomial k) (RatFunc k)).comp (C : k →+* Polynomial k)

/-- A nonzero constant, as a unit of the local ring of `A¹_k` at the origin. -/
def constantUnit (c : kˣ) : (localRingAtOrigin k)ˣ :=
  Units.map ((algebraMap (Polynomial k) (localRingAtOrigin k)).comp
    (C : k →+* Polynomial k)).toMonoidHom c

/-- A nonzero constant, read in the field of rational functions through the local ring at the
origin, is the constant read there directly. -/
theorem units_map_algebraMap_constantUnit (c : kˣ) :
    Units.map (algebraMap (localRingAtOrigin k) (RatFunc k)).toMonoidHom
        (constantUnit c) =
      Units.map (constantsHom k).toMonoidHom c :=
  Units.ext
    (IsScalarTower.algebraMap_apply (Polynomial k) (localRingAtOrigin k)
      (RatFunc k) (C (c : k))).symm

/-- The residue at the origin of a nonzero constant is that constant. -/
theorem units_map_residue_constantUnit (c : kˣ) :
    Units.map (residue (localRingAtOrigin k)).toMonoidHom (constantUnit c) =
      Units.map (residueFieldAtOriginEquiv k : k →* ResidueField (localRingAtOrigin k)) c :=
  Units.ext rfl

/-! ### The inclusion of the constants and its retraction -/

/-- **The inclusion of the constants, `K^M_n(k) ⟶ K^M_n(k(X))`.** -/
def constantInclusion (n : ℕ) :
    MilnorKTheory k n →+ MilnorKTheory (RatFunc k) n :=
  milnorKTransport (constantsHom k) n

/-- The retraction, read on the whole Milnor K-ring: multiply by the symbol of the uniformizer
`X`, take the tame symbol at the origin, and read the result in `k`. -/
def constantRetractionRing (k : Type u) [Field k] :
    MilnorKRing (RatFunc k) →+ MilnorKRing k :=
  ((milnorKRingMap ((residueFieldAtOriginEquiv k).symm :
          ResidueField (localRingAtOrigin k) →+* k)).toAddMonoidHom.comp
      ((MilnorKShift.shiftHom (ResidueField (localRingAtOrigin k))).comp
        (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_X (k := k))).toAddMonoidHom)).comp
    (AddMonoidHom.mulRight (milnorKSymbol (RatFunc k)
      (dvrFracUniformizer (RatFunc k) (irreducible_algebraMap_X (k := k)))))

/-- **The retraction of the inclusion of the constants, `K^M_n(k(X)) ⟶ K^M_n(k)`.** -/
def constantRetraction (n : ℕ) :
    MilnorKTheory (RatFunc k) n →+ MilnorKTheory k n :=
  ((milnorKTransportEquiv (residueFieldAtOriginEquiv k) n).symm.toAddMonoidHom.comp
      (dvrMilnorTameSymbol (F := RatFunc k)
        (irreducible_algebraMap_X (k := k)) n)).comp
    (milnorKMulSymbol (RatFunc k) n
      (dvrFracUniformizer (RatFunc k) (irreducible_algebraMap_X (k := k))))

/-- On the Milnor K-ring, `constantRetraction n` is `constantRetractionRing k`. -/
theorem coe_constantRetraction (n : ℕ) (β : MilnorKTheory (RatFunc k) n) :
    (constantRetraction n β : MilnorKRing k) =
      constantRetractionRing k (β : MilnorKRing (RatFunc k)) :=
  rfl

/-- The tame symbol at the origin of a symbol of units of the local ring there, multiplied by the
uniformizer: the ring-level form of `Stacks.Chow.dvrMilnorTameSymbol_uniformizer`. -/
theorem shift_dvrMilnorShiftMap_unitSymbolProd_mul_uniformizer
    (l : List (localRingAtOrigin k)ˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
        (irreducible_algebraMap_X (k := k))
        (unitSymbolProd (RatFunc k) l *
          milnorKSymbol (RatFunc k)
            (dvrFracUniformizer (RatFunc k)
              (irreducible_algebraMap_X (k := k))))) =
      residueSymbolProd (localRingAtOrigin k) l := by
  have hmem : unitSymbolProd (RatFunc k) l *
      milnorKSymbol (RatFunc k)
        (dvrFracUniformizer (RatFunc k)
          (irreducible_algebraMap_X (k := k))) ∈
      milnorKGrading (RatFunc k) (l.length + 1) := by
    refine SetLike.mul_mem_graded ?_ (milnorKSymbol_mem_milnorKGrading _)
    simpa only [unitSymbolProd, List.length_map] using
      milnorKSymbolProd_mem_milnorKGrading
        (l.map (Units.map (algebraMap (localRingAtOrigin k) (RatFunc k) :
          localRingAtOrigin k →* RatFunc k)))
  exact dvrMilnorTameSymbol_uniformizer (irreducible_algebraMap_X (k := k)) l.length
    (y := ⟨_, hmem⟩) l rfl

/-- A symbol of nonzero constants of `k`, read in the field of rational functions, is the symbol
of the corresponding units of the local ring at the origin. -/
theorem milnorKSymbolProd_constants_eq_unitSymbolProd (l : List kˣ) :
    milnorKSymbolProd (RatFunc k)
        (l.map (Units.map (constantsHom k).toMonoidHom)) =
      unitSymbolProd (RatFunc k) (l.map constantUnit) := by
  simp only [unitSymbolProd, List.map_map]
  exact congrArg _ (List.map_congr_left fun c _ ↦ (units_map_algebraMap_constantUnit c).symm)

/-- The retraction returns a symbol product of constants unchanged. -/
theorem constantRetractionRing_milnorKRingMap_constantsHom (l : List kˣ) :
    constantRetractionRing k (milnorKRingMap (constantsHom k) (milnorKSymbolProd k l)) =
      milnorKSymbolProd k l := by
  have hy : milnorKRingMap (constantsHom k) (milnorKSymbolProd k l) =
      unitSymbolProd (RatFunc k) (l.map constantUnit) :=
    (milnorKRingMap_milnorKSymbolProd (constantsHom k) l).trans
      (milnorKSymbolProd_constants_eq_unitSymbolProd l)
  change milnorKRingMap ((residueFieldAtOriginEquiv k).symm :
        ResidueField (localRingAtOrigin k) →+* k)
      (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
        (irreducible_algebraMap_X (k := k))
        (milnorKRingMap (constantsHom k) (milnorKSymbolProd k l) *
          milnorKSymbol (RatFunc k)
            (dvrFracUniformizer (RatFunc k)
              (irreducible_algebraMap_X (k := k)))))) = _
  rw [hy, shift_dvrMilnorShiftMap_unitSymbolProd_mul_uniformizer]
  simp only [residueSymbolProd, milnorKRingMap_milnorKSymbolProd, List.map_map]
  refine (congrArg _ (List.map_congr_left fun c _ ↦ ?_)).trans (congrArg _ (List.map_id l))
  change Units.map ((residueFieldAtOriginEquiv k).symm :
      ResidueField (localRingAtOrigin k) →* k)
      (Units.map (residue (localRingAtOrigin k)).toMonoidHom (constantUnit c)) = id c
  rw [units_map_residue_constantUnit]
  exact Units.ext ((residueFieldAtOriginEquiv k).symm_apply_apply (c : k))

/-- **The inclusion of the constants is split injective.** -/
theorem constantRetraction_constantInclusion (n : ℕ) (α : MilnorKTheory k n) :
    constantRetraction n (constantInclusion n α) = α :=
  Subtype.ext (coe_mem_of_forall_milnorKSymbolProd_mem
    (H := AddMonoidHom.eqLocus ((constantRetractionRing k).comp
      (milnorKRingMap (constantsHom k)).toAddMonoidHom) (AddMonoidHom.id (MilnorKRing k)))
    (fun l ↦ constantRetractionRing_milnorKRingMap_constantsHom l) α)

/-- **The Milnor K-theory of `k` is a subgroup of that of the rational function field `k(X)`.** -/
theorem constantInclusion_injective (n : ℕ) :
    Function.Injective (constantInclusion (k := k) n) :=
  Function.LeftInverse.injective (constantRetraction_constantInclusion n)

end Stacks.Chow

end
