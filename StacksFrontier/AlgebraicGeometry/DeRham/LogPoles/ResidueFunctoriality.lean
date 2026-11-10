module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ComplexFunctoriality

/-!
# The residue of the de Rham complex of log poles is functorial in the ring

Let `A → R` be a ring map, let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`, and let `R → R'` be a further map of `A`-algebras carrying
`t` to an equation `s` of the pulled-back divisor `Y' = Spec (R' ⧸ (s))` in `X' = Spec R'`.
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ComplexFunctoriality` builds the induced map
`Ω^•_{X/S}(log Y) ⟶ Ω^•_{X'/S}(log Y')` and shows that it restricts on the forms with no pole to
the standard map of de Rham complexes. This file supplies the remaining square, compatibility
with the residue:

```
0 ⟶ Ω^•_{X/S}  ⟶ Ω^•_{X/S}(log Y)  ⟶ Ω^•_{Y/S}[-1]  ⟶ 0
        |                |                  |
0 ⟶ Ω^•_{X'/S} ⟶ Ω^•_{X'/S}(log Y') ⟶ Ω^•_{Y'/S}[-1] ⟶ 0
```

and so assembles the two residue sequences of Stacks Tag 0FMW, affine locally, into a morphism of
short exact sequences of complexes.

## Main definitions

* `Stacks.LogPoles.deRhamShiftTowerMap`: the shifted de Rham complex `Ω^•_{B/A}[-1]` is functorial
  in `B`, the right-hand column of the square.
* `Stacks.LogPoles.quotientTowerAlgebra`: **the algebra structure on `R' ⧸ (s)` over `R ⧸ (t)`**
  induced by `R → R'` when `s` is the image of `t`, i.e. the map of divisors `Y' → Y`.
* `Stacks.LogPoles.logShortComplexTowerHom`: **the morphism of the two residue sequences.**

## Main results

* `Stacks.LogPoles.logComplexTowerMap_comp_logResidue`: **the residue square commutes.** This is
  the remaining square, the one the inclusion square of `ComplexFunctoriality` does not give.
* `Stacks.LogPoles.isScalarTower_base_quotientTowerAlgebra` and
  `Stacks.LogPoles.isScalarTower_mid_quotientTowerAlgebra`: the two scalar towers carried by the
  induced algebra structure on the divisors, which discharge the hypotheses of the square.
* `Stacks.LogPoles.surjective_logResidue_comp_deRhamShiftTowerMap_f_succ`: the lower-left leg of
  the square is surjective in every positive degree whenever the restriction of forms to the
  divisors is, so the square is not commutative for the degenerate reason that a leg vanishes.
* `Stacks.LogPoles.deRhamShiftTowerMap_comp`: the right-hand column composes along a tower, the
  presheaf law matching `Stacks.LogPoles.logComplexTowerMap_comp` for the middle column.

## Implementation notes

The square needs the induced algebra structure `Algebra (R ⧸ (t)) (R' ⧸ (s))` and the two scalar
towers `IsScalarTower A (R ⧸ (t)) (R' ⧸ (s))` and `IsScalarTower R (R ⧸ (t)) (R' ⧸ (s))`, and
these are carried as instance hypotheses rather than built from the hypothesis `s = algebraMap R
R' t` inside the statement: a definition may not take a propositional hypothesis as an instance
argument, and `R' ⧸ (s)` is not syntactically a quotient of `R'` by the pushforward of `(t)`, so
Mathlib's global `Ideal.Quotient.algebraQuotientMapQuotient` does not apply either. They are not
an assumption of the conclusion: the two towers pin the carried algebra structure down to the
canonical one, because `R → R ⧸ (t)` is surjective, and
`Stacks.LogPoles.quotientTowerAlgebra` together with the two `isScalarTower_*` theorems
discharges all three from `s = algebraMap R R' t` alone. The `_of_eq` forms of the square and of
the morphism of sequences do exactly that and carry no instance hypotheses.

There is no instance diamond on `Algebra A (R' ⧸ (s))`, because `Algebra` is not transitive as an
instance in Mathlib: the only instance is `Ideal.Quotient.algebra` along `A → R' → R' ⧸ (s)`, and
instance search never composes it with a carried `Algebra (R ⧸ (t)) (R' ⧸ (s))`. The agreement of
that path with the path `A → R ⧸ (t) → R' ⧸ (s)` is therefore not a definitional clash to be
avoided but a proposition to be proved, and it is exactly
`IsScalarTower A (R ⧸ (t)) (R' ⧸ (s))`; `isScalarTower_base_quotientTowerAlgebra` proves it.
The same remark applies to `Algebra R (R' ⧸ (s))` and `isScalarTower_mid_quotientTowerAlgebra`.

The mathematical content of the square is small once the maps exist: the residue of a form
`ω + dlog t ∧ η` is `η|_Y`, so both legs send the pair `(ω, η)` to the restriction of `η` to
`Y'`, reached along `Y' → Y → X` on one side and along `Y' → X' → X` on the other. That the two
agree is `KaehlerDifferential.mapExteriorPower_mapExteriorPower` applied to the two towers
`R → R ⧸ (t) → R' ⧸ (s)` and `R → R' → R' ⧸ (s)`, whose composites are the same map of forms. The
splitting hypothesis of Stacks Tag 0FMV is needed on both sides, since it is what makes each
residue well defined, but it plays no further role: nothing is assumed relating the two
retractions.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), the residue sequence
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

/-! ### Functoriality of the shifted de Rham complex -/

section Shift

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The degreewise map of the shifted de Rham complexes `Ω^•_{B/A}[-1] → Ω^•_{C/A}[-1]` induced by
a tower `B → C` of `A`-algebras: zero in degree zero, and the restriction of forms in degree
`p + 1`. -/
def deRhamShiftTowerF : (p : ℕ) → ((LaurentDeRham.deRhamComplexShift A B).X p ⟶
      (LaurentDeRham.deRhamComplexShift A C).X p)
  | 0 => 0
  | p + 1 => ModuleCat.ofHom ((mapExteriorPower A B C p).restrictScalars A)

/-- In degree `p + 1`, `deRhamShiftTowerF` is the map of exterior powers `mapExteriorPower`. -/
@[simp]
theorem deRhamShiftTowerF_succ_apply (p : ℕ) (ω : ↥(⋀[B]^p (Ω[B⁄A]))) :
    (deRhamShiftTowerF A B C (p + 1)).hom ω = mapExteriorPower A B C p ω := rfl

/-- **The shifted de Rham complex is functorial in the algebra variable**: a tower `B → C` of
`A`-algebras induces `Ω^•_{B/A}[-1] ⟶ Ω^•_{C/A}[-1]`. The differential of the shift is `-d`, and
the restriction of forms commutes with `d`, hence with `-d`. -/
def deRhamShiftTowerMap :
    LaurentDeRham.deRhamComplexShift A B ⟶ LaurentDeRham.deRhamComplexShift A C :=
  CochainComplex.ofHom (deRhamShiftTowerF A B C) fun p ↦ by
    cases p with
    | zero =>
        change deRhamShiftTowerF A B C 0 ≫ (LaurentDeRham.deRhamComplexShift A C).d 0 1 =
          (LaurentDeRham.deRhamComplexShift A B).d 0 1 ≫ deRhamShiftTowerF A B C 1
        rw [LaurentDeRham.deRhamComplexShift_d_zero, LaurentDeRham.deRhamComplexShift_d_zero,
          Limits.comp_zero, Limits.zero_comp]
    | succ q =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[B]^q (Ω[B⁄A]), y = ω := ⟨ω, rfl⟩
        change ((LaurentDeRham.deRhamComplexShift A C).d (q + 1) (q + 1 + 1)).hom
            ((deRhamShiftTowerF A B C (q + 1)).hom ω) =
          (deRhamShiftTowerF A B C (q + 1 + 1)).hom
            (((LaurentDeRham.deRhamComplexShift A B).d (q + 1) (q + 1 + 1)).hom ω)
        rw [LaurentDeRham.deRhamComplexShift_d_succ, LaurentDeRham.deRhamComplexShift_d_succ]
        change -deRhamDifferential (A := A) (B := C) q (mapExteriorPower A B C q ω) =
          mapExteriorPower A B C (q + 1) (-deRhamDifferential (A := A) (B := B) q ω)
        rw [map_neg, mapExteriorPower_deRhamDifferential]

/-- The degree-`p` component of `deRhamShiftTowerMap` is `deRhamShiftTowerF`. -/
@[simp]
theorem deRhamShiftTowerMap_f (p : ℕ) :
    (deRhamShiftTowerMap A B C).f p = deRhamShiftTowerF A B C p := rfl

end Shift

section ShiftComp

variable (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B C] [Algebra B D] [Algebra C D]
  [IsScalarTower A B C] [IsScalarTower A B D] [IsScalarTower A C D] [IsScalarTower B C D]

/-- **The maps of the shifted de Rham complexes compose along a tower** `B → C → D`. This is the
presheaf law for the right-hand column of the residue square, matching
`Stacks.LogPoles.logComplexTowerMap_comp` for the middle column. -/
theorem deRhamShiftTowerMap_comp :
    deRhamShiftTowerMap A B C ≫ deRhamShiftTowerMap A C D = deRhamShiftTowerMap A B D := by
  ext p : 1
  cases p with
  | zero => exact (Limits.isZero_zero (ModuleCat.{u} A)).eq_of_src _ _
  | succ q =>
      ext ω
      obtain ⟨ω, rfl⟩ : ∃ y : ⋀[B]^q (Ω[B⁄A]), y = ω := ⟨ω, rfl⟩
      change (deRhamShiftTowerF A C D (q + 1)).hom ((deRhamShiftTowerF A B C (q + 1)).hom ω) =
        (deRhamShiftTowerF A B D (q + 1)).hom ω
      exact mapExteriorPower_mapExteriorPower A B C D q ω

end ShiftComp

/-! ### The induced algebra structure on the divisors -/

section QuotientTower

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}

/-- **The map of divisors `Y' → Y`**: if `s` is the image of `t` under `R → R'`, then `(t)` is
carried into `(s)`, so `R' ⧸ (s)` is an algebra over `R ⧸ (t)`. This is the algebra structure the
residue square needs, and it is not an instance: it is produced from the hypothesis
`s = algebraMap R R' t`, which instance search cannot find. -/
@[instance_reducible]
def quotientTowerAlgebra (hs : s = algebraMap R R' t) :
    Algebra (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (R := R) (A := R') (p := Ideal.span {t}) (P := Ideal.span {s}) <| by
  rw [Ideal.span_le]
  rintro x (rfl : x = t)
  simp [hs]

/-- The map of divisors is the map `R → R'` on representatives. -/
theorem quotientTowerAlgebra_algebraMap (hs : s = algebraMap R R' t) (x : R) :
    letI := quotientTowerAlgebra hs
    algebraMap (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R R' x) := rfl

/-- **The two routes from the base to the divisor `Y'` agree.** The structure map `A → R' ⧸ (s)`
of the canonical instance goes `A → R' → R' ⧸ (s)`; composing the map of divisors with
`A → R ⧸ (t)` goes `A → R → R' → R' ⧸ (s)`. These are equal because `A → R → R'` is `A → R'`.
This is the comparison of the two paths to `Algebra A (R' ⧸ (s))`, stated as the proposition it
is rather than as a clash of instances. -/
theorem isScalarTower_base_quotientTowerAlgebra (hs : s = algebraMap R R' t) :
    letI := quotientTowerAlgebra hs
    IsScalarTower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) :=
  let := quotientTowerAlgebra hs
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A R (R ⧸ Ideal.span {t}) x,
      Ideal.Quotient.algebraMap_eq, quotientTowerAlgebra_algebraMap hs,
      ← IsScalarTower.algebraMap_apply A R R' x]
    rfl

/-- **The two routes from `R` to the divisor `Y'` agree**: the structure map `R → R' ⧸ (s)` is
`R → R' → R' ⧸ (s)`, and composing the map of divisors with `R → R ⧸ (t)` gives the same. -/
theorem isScalarTower_mid_quotientTowerAlgebra (hs : s = algebraMap R R' t) :
    letI := quotientTowerAlgebra hs
    IsScalarTower R (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) :=
  let := quotientTowerAlgebra hs
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [Ideal.Quotient.algebraMap_eq, quotientTowerAlgebra_algebraMap hs]
    rfl

end QuotientTower

/-! ### The residue square -/

section Square

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}
  [Algebra (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower R (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]

/-- The two routes from the forms on `X` to the forms on the divisor `Y'` agree: restricting to
`Y` and then along `Y' → Y` is restricting to `X'` and then to `Y'`. Both are the restriction
along `R → R' ⧸ (s)`. This is the whole content of the residue square. -/
theorem mapExteriorPower_quotient_comm (p : ℕ) (ω : ↥(⋀[R]^p (Ω[R⁄A]))) :
    mapExteriorPower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) p
        (mapExteriorPower A R (R ⧸ Ideal.span {t}) p ω) =
      mapExteriorPower A R' (R' ⧸ Ideal.span {s}) p (mapExteriorPower A R R' p ω) := by
  rw [mapExteriorPower_mapExteriorPower, mapExteriorPower_mapExteriorPower]

/-- **The residue square commutes.** Taking a form with a logarithmic pole along `Y` to `X'` and
then taking its residue along `Y'` is taking its residue along `Y` and then restricting that form
to `Y'`. Together with
`Stacks.LogPoles.logIncl_comp_logComplexTowerMap` this makes the induced maps a morphism of the
two residue sequences of Stacks Tag 0FMW. -/
theorem logComplexTowerMap_comp_logResidue (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    logComplexTowerMap hs ht hs' ≫ logResidue hs' hsplit' =
      logResidue ht hsplit ≫
        deRhamShiftTowerMap A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) := by
  ext p : 1
  cases p with
  | zero =>
      exact (Limits.isZero_zero (ModuleCat.{u} A)).eq_of_tgt _ _
  | succ q =>
      ext z
      obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
          Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change (logResidueF hs' hsplit' (q + 1)).hom
            ((logFormsTowerMap hs ht hs' (q + 1)).hom
              (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) =
          (deRhamShiftTowerF A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) (q + 1)).hom
            ((logResidueF ht hsplit (q + 1)).hom
              (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x))
      rw [logFormsTowerMap_succ_apply, logResidueF_succ_apply, logResidueF_succ_apply,
        deRhamShiftTowerF_succ_apply, logPairTowerMap_apply]
      exact (mapExteriorPower_quotient_comm q x.2).symm

end Square

/-! ### The value of the square, and that no leg of it vanishes -/

section Value

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}

/-- The value of either leg of the residue square on a form with a logarithmic pole: the pair
`(ω, η)` goes to the restriction of `η` to the divisor `Y'`. In particular neither leg is the
zero map, and `(0, η)` already realises every restricted form. -/
@[simp]
theorem logResidue_logComplexTowerMap_apply (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id)
    (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    ((logResidue hs' hsplit').f (p + 1)).hom
        (((logComplexTowerMap hs ht hs').f (p + 1)).hom
          (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) x)) =
      mapExteriorPower A R' (R' ⧸ Ideal.span {s}) p (mapExteriorPower A R R' p x.2) := rfl

end Value

section NonVacuity

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] {t : R} {s : R'}
  [Algebra (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]

/-- **The lower-left leg of the residue square is surjective in every positive degree** whenever
the restriction of forms from `Y` to `Y'` is — as it is for a localization. So the square does
not commute for the degenerate reason that one of its legs vanishes: the residue is surjective in
positive degrees already on `Y`, and the restriction to `Y'` keeps it so. -/
theorem surjective_logResidue_comp_deRhamShiftTowerMap_f_succ
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsurj : ∀ p : ℕ, Function.Surjective
      (mapExteriorPower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) p)) (p : ℕ) :
    Function.Surjective
      (((logResidue ht hsplit ≫
        deRhamShiftTowerMap A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})).f (p + 1)).hom) := by
  intro ζ
  obtain ⟨η, rfl⟩ := hsurj p ζ
  obtain ⟨y, hy⟩ := surjective_logResidue_f_succ ht hsplit p η
  exact ⟨y, congrArg (mapExteriorPower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) p) hy⟩

end NonVacuity

/-! ### The morphism of the two residue sequences -/

section Morphism

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}
  [Algebra (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower R (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]

/-- **The upper-right leg of the residue square is surjective in every positive degree** too,
whenever the restriction of forms from `Y` to `Y'` is. This is the square applied: the residue of
`Ω^•_{X'/S}(log Y')` along `Y'` already hits everything on the image of the restriction map, and
it does so on the forms coming from `X`. Together with
`Stacks.LogPoles.surjective_logResidue_comp_deRhamShiftTowerMap_f_succ` this shows the square is
not commutative because one of its legs vanishes. -/
theorem surjective_logResidue_comp_logComplexTowerMap_f_succ (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id)
    (hsurj : ∀ p : ℕ, Function.Surjective
      (mapExteriorPower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) p)) (p : ℕ) :
    Function.Surjective
      (((logComplexTowerMap hs ht hs' ≫ logResidue hs' hsplit').f (p + 1)).hom) := by
  rw [logComplexTowerMap_comp_logResidue hs ht hs' hsplit hsplit']
  exact surjective_logResidue_comp_deRhamShiftTowerMap_f_succ ht hsplit hsurj p

/-- **The morphism of the two residue sequences of Stacks Tag 0FMW**, affine locally: the
standard map of de Rham complexes on the forms with no pole, the induced map of the complexes of
log poles in the middle, and the restriction of forms to the divisor on the right. -/
def logShortComplexTowerHom (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    logShortComplex ht hsplit ⟶ logShortComplex hs' hsplit' where
  τ₁ := KaehlerDifferential.deRhamComplexMap A R R'
  τ₂ := logComplexTowerMap hs ht hs'
  τ₃ := deRhamShiftTowerMap A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})
  comm₁₂ := (logIncl_comp_logComplexTowerMap hs ht hs').symm
  comm₂₃ := logComplexTowerMap_comp_logResidue hs ht hs' hsplit hsplit'

/-- The middle component of `logShortComplexTowerHom` is `logComplexTowerMap`. -/
@[simp]
theorem logShortComplexTowerHom_τ₂ (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    (logShortComplexTowerHom hs ht hs' hsplit hsplit').τ₂ = logComplexTowerMap hs ht hs' := rfl

end Morphism

/-! ### The square with its instance hypotheses discharged -/

section Discharged

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}

/-- **The residue square, with no carried instances.** The algebra structure on the divisors and
the two scalar towers it must satisfy are all produced from `s = algebraMap R R' t`, so the
commuting square of
`Stacks.LogPoles.logComplexTowerMap_comp_logResidue` holds under exactly the hypotheses of
`Stacks.LogPoles.logComplexTowerMap` and of the two residues. -/
theorem logComplexTowerMap_comp_logResidue_of_eq (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    letI := quotientTowerAlgebra hs
    letI := isScalarTower_base_quotientTowerAlgebra (A := A) hs
    letI := isScalarTower_mid_quotientTowerAlgebra hs
    logComplexTowerMap hs ht hs' ≫ logResidue hs' hsplit' =
      logResidue ht hsplit ≫
        deRhamShiftTowerMap A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}) :=
  let := quotientTowerAlgebra hs
  let := isScalarTower_base_quotientTowerAlgebra (A := A) hs
  let := isScalarTower_mid_quotientTowerAlgebra hs
  logComplexTowerMap_comp_logResidue hs ht hs' hsplit hsplit'

/-- **The morphism of the two residue sequences of Stacks Tag 0FMW, with no carried instances.**
This is the direct input to the naturality of the connecting map `δ` of Stacks Tag 0FUQ: it
exhibits the restriction maps of `Ω^•(log Y)` as a morphism of the short exact sequences
whose triangles `δ` is built from. -/
def logShortComplexTowerHom_of_eq (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    letI := quotientTowerAlgebra hs
    letI := isScalarTower_base_quotientTowerAlgebra (A := A) hs
    letI := isScalarTower_mid_quotientTowerAlgebra hs
    logShortComplex ht hsplit ⟶ logShortComplex hs' hsplit' :=
  letI := quotientTowerAlgebra hs
  letI := isScalarTower_base_quotientTowerAlgebra (A := A) hs
  letI := isScalarTower_mid_quotientTowerAlgebra hs
  logShortComplexTowerHom hs ht hs' hsplit hsplit'

end Discharged

end Stacks.LogPoles

end
