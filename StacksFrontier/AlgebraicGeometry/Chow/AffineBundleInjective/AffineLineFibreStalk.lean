module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.AffineLineFibreAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary

/-!
# The local rings of the closure of the generic point of a fibre of `Spec A[T] ⟶ Spec A`

Let `A` be a commutative ring, `y` a point of `Spec A` with prime `𝔭` and residue field `κ(y)`,
and let `f : Spec A[T] ⟶ Spec A` be the projection. The fibre of `f` over `y` is the affine line
over `κ(y)`. Its generic point `ζ` is the prime `𝔭 A[T]`
(`Stacks.Chow.fibreGenericPoint`); every other point `w` of the fibre is a closed point of that
affine line, the prime `fibrePrime ζ w` of `κ(y)[T]` obtained by extending the prime of `w`.

This file identifies the scheme-theoretic objects attached to `ζ` and `w` with the algebraic ones
of the affine line over `κ(y)`:

* the residue field `κ(ζ)` is the field of rational functions `κ(y)(T)`
  (`Stacks.Chow.fibreGenericResidueFieldEquiv`): it is a fraction field of `κ(y)[T]`, through
  evaluation at `ζ`;
* the local ring of the integral closed subscheme `closure {ζ}` at `w` is the local ring of the
  affine line over `κ(y)` at `fibrePrime ζ w`, compatibly with the identification of fraction
  fields (`Stacks.Chow.exists_closureStalk_ringEquiv`). Both are subrings of the same field, the
  fractions with denominators off the prime, and the identification of fraction fields carries one
  onto the other. In particular it is a discrete valuation ring
  (`Stacks.Chow.isDiscreteValuationRing_closureStalk`).

## Main definitions

* `Stacks.Chow.specEval` — the value at a point of `Spec R` of an element of `R`.
* `Stacks.Chow.fibreGenericPoint` — the generic point `𝔭 A[T]` of the fibre over `y`.
* `Stacks.Chow.IsGenericFibrePoint` — a point is the generic point of its fibre.
* `Stacks.Chow.fibreGenericResidueFieldEquiv` — `κ(ζ) ≃+* κ(y)(T)`.
* `Stacks.Chow.fibrePrime` — the closed point of the affine line attached to a point of the fibre.

## Main results

* `Stacks.Chow.eq_fibreGenericPoint_of_specializes` — a proper specialization inside a fibre
  starts at the generic point of the fibre.
* `Stacks.Chow.exists_closureStalk_ringEquiv` — the local ring of `closure {ζ}` at `w` is the
  local ring of the affine line at `fibrePrime ζ w`.
* `Stacks.Chow.isDiscreteValuationRing_closureStalk` — that local ring is a discrete valuation
  ring.
* `Stacks.Chow.exists_fibrePrime_eq`, `Stacks.Chow.eq_of_fibrePrime_eq` — the closed points of
  the fibre are exactly the closed points of the affine line over `κ(y)`.
* `Stacks.Chow.ordFrac_fibreGenericResidueFieldEquiv_eq_one` — an order of vanishing zero on
  `closure {ζ}` at `w` is an order zero on the affine line at `fibrePrime ζ w`.

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial

universe u

namespace Stacks.Chow

/-! ### Germs and values of global functions on an affine scheme -/

section SpecGerm

variable {R : CommRingCat.{u}}

/-- The prime of a point of `Spec R` is prime, available to instance search. -/
private instance isPrime_asIdeal_spec (x : Spec R) : x.asIdeal.IsPrime := x.isPrime

/-- The value at a point `x` of `Spec R` of an element of `R`: its germ, read in `κ(x)`. -/
def specEval (x : Spec R) : R →+* (Spec R).residueField x :=
  ((Spec R).residue x).hom.comp ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial).hom

/-- The germ at `x` of an element `r` of `R` is the image of `r` in the localization of `R` at the
prime of `x`, under the identification of the stalk with that localization. -/
theorem germ_ΓSpecIso_inv_eq (x : Spec R) (r : R) :
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) r =
      (Spec.stalkIso R x).inv (algebraMap R _ r) :=
  (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Spec.algebraMap_stalkIso_inv (x := x))) r).symm

/-- The value of `r` at `x` is the residue in `κ(x)` of the germ of `r` at `x`. -/
theorem specEval_apply (x : Spec R) (r : R) :
    specEval x r =
      (Spec R).residue x (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) r) := rfl

/-- The germ of `r` at `x` is a unit if and only if `r` does not vanish at `x`. -/
theorem isUnit_germ_ΓSpecIso_inv_iff (x : Spec R) (r : R) :
    IsUnit (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) r) ↔ r ∉ x.asIdeal := by
  rw [germ_ΓSpecIso_inv_eq]
  exact (MulEquiv.isUnit_map
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm.toMulEquiv).trans
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime x.asIdeal) x.asIdeal r)

/-- Every germ at `x` is a fraction of germs of elements of `R`, with denominator not vanishing at
`x`. -/
theorem exists_mul_germ_ΓSpecIso_inv_eq (x : Spec R) (z : (Spec R).presheaf.stalk x) :
    ∃ a b : R, b ∉ x.asIdeal ∧
      z * ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) b =
        ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) a := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj x.asIdeal.primeCompl
    ((Spec.stalkIso R x).hom z)
  refine ⟨a, b, b.2, ?_⟩
  have h := congrArg (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm hab
  rw [map_mul] at h
  rw [germ_ΓSpecIso_inv_eq, germ_ΓSpecIso_inv_eq]
  convert h using 2
  · exact (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm_apply_apply z |>.symm
  all_goals rfl

/-- The value of `r` at `x` vanishes if and only if `r` lies in the prime of `x`. -/
theorem specEval_eq_zero_iff (x : Spec R) (r : R) : specEval x r = 0 ↔ r ∈ x.asIdeal := by
  rw [← not_iff_not, ← isUnit_germ_ΓSpecIso_inv_iff]
  exact IsLocalRing.residue_ne_zero_iff_isUnit
    (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) r)

/-- Every element of `κ(x)` is a fraction of values of elements of `R`, with denominator not
vanishing at `x`. -/
theorem exists_mul_specEval_eq (x : Spec R) (c : (Spec R).residueField x) :
    ∃ a b : R, b ∉ x.asIdeal ∧ c * specEval x b = specEval x a := by
  obtain ⟨z, rfl⟩ := (Spec R).residue_surjective x c
  obtain ⟨a, b, hb, h⟩ := exists_mul_germ_ΓSpecIso_inv_eq x z
  exact ⟨a, b, hb, by rw [specEval_apply, specEval_apply, ← map_mul, h]⟩

variable {S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Germs of global functions are natural along `Spec S ⟶ Spec R`. -/
theorem stalkMap_germ_ΓSpecIso_inv (p : Spec S) (r : R) :
    (Spec.map φ).stalkMap p
        (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ ((Spec.map φ) p) trivial) r) =
      ((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.germ ⊤ p trivial) (φ r) := by
  have h2 : (Scheme.ΓSpecIso S).inv (φ r) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) :=
    DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Scheme.ΓSpecIso_inv_naturality φ)) r
  change (Spec.map φ).stalkMap p ((Spec R).presheaf.germ ⊤ _ trivial
      ((Scheme.ΓSpecIso R).inv r)) = (Spec S).presheaf.germ ⊤ p trivial
      ((Scheme.ΓSpecIso S).inv (φ r))
  refine (Scheme.Hom.germ_stalkMap_apply (Spec.map φ) ⊤ p trivial _).trans ?_
  rw [h2]
  rfl

/-- Values of global functions are natural along `Spec S ⟶ Spec R`. -/
theorem residueFieldMap_specEval (p : Spec S) (r : R) :
    (Spec.map φ).residueFieldMap p (specEval ((Spec.map φ) p) r) = specEval p (φ r) := by
  rw [specEval_apply, specEval_apply, ← stalkMap_germ_ΓSpecIso_inv]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
    (Scheme.residue_residueFieldMap (Spec.map φ) p)) _

end SpecGerm

/-! ### The fibres of `Spec A[T] ⟶ Spec A` -/

section Fibre

attribute [local instance] isIntegral_integralComponentAt

variable {A : CommRingCat.{u}}

/-- The point of `Spec A[T]` lying over a point of `Spec A`, as a prime ideal: the contraction. -/
theorem asIdeal_specMap_C_base (x : Spec (CommRingCat.of (Polynomial A))) :
    ((Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base x).asIdeal =
      x.asIdeal.comap (C : A →+* Polynomial A) := rfl

/-- **The generic point of the fibre over `y`**: the prime `𝔭 A[T]`, for `𝔭` the prime of `y`. -/
def fibreGenericPoint (y : Spec A) : Spec (CommRingCat.of (Polynomial A)) :=
  ⟨y.asIdeal.map (C : A →+* Polynomial A), @Ideal.isPrime_map_C_of_isPrime _ _ _ y.isPrime⟩

/-- The prime of the generic point of the fibre over `y` is the extension `𝔭 A[T]` of the prime
`𝔭` of `y`. -/
theorem asIdeal_fibreGenericPoint (y : Spec A) :
    (fibreGenericPoint y).asIdeal = y.asIdeal.map (C : A →+* Polynomial A) := rfl

/-- The generic point of the fibre over `y` lies over `y`. -/
theorem specMap_C_base_fibreGenericPoint (y : Spec A) :
    (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base (fibreGenericPoint y) = y := by
  refine PrimeSpectrum.ext (Ideal.ext fun a ↦ ?_)
  rw [asIdeal_specMap_C_base, asIdeal_fibreGenericPoint, Ideal.mem_comap]
  exact ⟨fun h ↦ by simpa using Ideal.mem_map_C_iff.mp h 0, Ideal.mem_map_of_mem _⟩

/-- The generic point of the fibre over `y` specializes to every point of that fibre. -/
theorem fibreGenericPoint_specializes {y : Spec A} {w : Spec (CommRingCat.of (Polynomial A))}
    (hw : (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base w = y) :
    fibreGenericPoint y ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes (fibreGenericPoint y) w).mp ?_
  change y.asIdeal.map C ≤ w.asIdeal
  rw [Ideal.map_le_iff_le_comap, ← asIdeal_specMap_C_base, hw]

/-- **A point of a fibre which specializes to another point of that fibre is the generic point of
the fibre, unless the two are equal.** -/
theorem eq_fibreGenericPoint_of_specializes {ζ w : Spec (CommRingCat.of (Polynomial A))}
    (hw : ζ ⤳ w)
    (hfib : (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base ζ =
      (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base w)
    (hne : ζ ≠ w) :
    ζ = fibreGenericPoint ((Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base ζ) := by
  set y := (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base ζ
  have : ζ.asIdeal.IsPrime := ζ.isPrime
  have : w.asIdeal.IsPrime := w.isPrime
  refine PrimeSpectrum.ext (eq_map_C_of_le_of_ne (specEval y) (𝔭 := y.asIdeal)
    (specEval_eq_zero_iff y) (exists_mul_specEval_eq y) (Q := w.asIdeal) ?_ rfl
    ((PrimeSpectrum.le_iff_specializes ζ w).mpr hw) fun h ↦ hne (PrimeSpectrum.ext h))
  rw [← asIdeal_specMap_C_base, ← hfib]

/-! ### The residue field at the generic point of a fibre -/

/-- The point of the base under a point of `Spec A[T]`. -/
abbrev specPolynomialBase (ζ : Spec (CommRingCat.of (Polynomial A))) : Spec A :=
  (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).base ζ

/-- The evaluation of polynomials over `κ(f ζ)` at the point `ζ` of `Spec A[T]`: constants go
through `κ(f ζ) → κ(ζ)` and the variable to the value of `T` at `ζ`. -/
def fibrePolynomialEval (ζ : Spec (CommRingCat.of (Polynomial A))) :
    Polynomial ((Spec A).residueField (specPolynomialBase ζ)) →+*
      (Spec (CommRingCat.of (Polynomial A))).residueField ζ :=
  eval₂RingHom ((Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).residueFieldMap ζ).hom
    (specEval ζ X)

/-- Evaluating the image in `κ(f ζ)[T]` of a polynomial over `A` is taking its value at `ζ`. -/
theorem fibrePolynomialEval_mapRingHom (ζ : Spec (CommRingCat.of (Polynomial A)))
    (h : Polynomial A) :
    fibrePolynomialEval ζ (mapRingHom (specEval (specPolynomialBase ζ)) h) = specEval ζ h := by
  have key : (fibrePolynomialEval ζ).comp (mapRingHom (specEval (specPolynomialBase ζ))) =
      specEval ζ := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, fibrePolynomialEval,
        coe_eval₂RingHom, eval₂_C]
      exact residueFieldMap_specEval (CommRingCat.ofHom (C : A →+* Polynomial A)) ζ a
    · rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X, fibrePolynomialEval,
        coe_eval₂RingHom, eval₂_X]
  exact DFunLike.congr_fun key h

/-- A point of `Spec A[T]` is **the generic point of its fibre** when its prime is extended from
the prime of its image. -/
def IsGenericFibrePoint (ζ : Spec (CommRingCat.of (Polynomial A))) : Prop :=
  ζ.asIdeal = (specPolynomialBase ζ).asIdeal.map (C : A →+* Polynomial A)

/-- The point `fibreGenericPoint y` is the generic point of its fibre. -/
theorem isGenericFibrePoint_fibreGenericPoint (y : Spec A) :
    IsGenericFibrePoint (fibreGenericPoint y) := by
  rw [IsGenericFibrePoint, specPolynomialBase, specMap_C_base_fibreGenericPoint]
  rfl

variable {ζ : Spec (CommRingCat.of (Polynomial A))}

/-- At the generic point of a fibre the evaluation of polynomials is injective: `T` is
transcendental over `κ(f ζ)` in `κ(ζ)`. -/
theorem fibrePolynomialEval_injective (hζ : IsGenericFibrePoint ζ) :
    Function.Injective (fibrePolynomialEval ζ) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨s, hs, h, hh⟩ := exists_C_mul_eq_mapRingHom (specEval (specPolynomialBase ζ))
    (exists_mul_specEval_eq (specPolynomialBase ζ)) g
  have h0 : specEval ζ h = 0 := by
    rw [← fibrePolynomialEval_mapRingHom, ← hh, map_mul, hg, mul_zero]
  rw [specEval_eq_zero_iff, hζ, ← mapRingHom_eq_zero_iff (specEval (specPolynomialBase ζ))
    (specEval_eq_zero_iff (specPolynomialBase ζ)), ← hh] at h0
  exact (mul_eq_zero.mp h0).resolve_left (C_ne_zero.mpr (mt (specEval_eq_zero_iff _ s).mp hs))

/-- The algebra structure of `κ(ζ)` over `κ(f ζ)[T]` given by evaluation. -/
@[instance_reducible]
def fibrePolynomialAlgebra (ζ : Spec (CommRingCat.of (Polynomial A))) :
    Algebra (Polynomial ((Spec A).residueField (specPolynomialBase ζ)))
      ((Spec (CommRingCat.of (Polynomial A))).residueField ζ) :=
  (fibrePolynomialEval ζ).toAlgebra

/-- **The residue field at the generic point of a fibre is the field of rational functions over
the residue field below.** -/
theorem isFractionRing_fibrePolynomialAlgebra (hζ : IsGenericFibrePoint ζ) :
    letI := fibrePolynomialAlgebra ζ
    IsFractionRing (Polynomial ((Spec A).residueField (specPolynomialBase ζ)))
      ((Spec (CommRingCat.of (Polynomial A))).residueField ζ) := by
  let _ := fibrePolynomialAlgebra ζ
  have hinj := fibrePolynomialEval_injective hζ
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · exact IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero y (hinj (by rwa [map_zero]))
  · have : ζ.asIdeal.IsPrime := ζ.isPrime
    obtain ⟨a, b, hb, h⟩ := exists_mul_specEval_eq ζ z
    have hb0 : mapRingHom (specEval (specPolynomialBase ζ)) b ≠ 0 := fun h0 ↦ hb (by
      rw [← specEval_eq_zero_iff, ← fibrePolynomialEval_mapRingHom, h0, map_zero])
    refine ⟨⟨mapRingHom (specEval (specPolynomialBase ζ)) a,
      ⟨mapRingHom (specEval (specPolynomialBase ζ)) b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, ?_⟩
    change z * fibrePolynomialEval ζ _ = fibrePolynomialEval ζ _
    rw [fibrePolynomialEval_mapRingHom, fibrePolynomialEval_mapRingHom, h]
  · exact ⟨1, by rw [hinj h]⟩

/-- **The residue field at the generic point of a fibre, identified with `RatFunc κ(f ζ)`.** -/
def fibreGenericResidueFieldEquiv (hζ : IsGenericFibrePoint ζ) :
    (Spec (CommRingCat.of (Polynomial A))).residueField ζ ≃+*
      RatFunc ((Spec A).residueField (specPolynomialBase ζ)) :=
  letI := fibrePolynomialAlgebra ζ
  haveI := isFractionRing_fibrePolynomialAlgebra hζ
  (IsLocalization.algEquiv
    (nonZeroDivisors (Polynomial ((Spec A).residueField (specPolynomialBase ζ))))
    ((Spec (CommRingCat.of (Polynomial A))).residueField ζ)
    (RatFunc ((Spec A).residueField (specPolynomialBase ζ)))).toRingEquiv

/-- On the evaluation at `ζ` of a polynomial over `κ(f ζ)`, the identification of `κ(ζ)` with
`κ(f ζ)(T)` is the inclusion of that polynomial. -/
theorem fibreGenericResidueFieldEquiv_fibrePolynomialEval (hζ : IsGenericFibrePoint ζ)
    (g : Polynomial ((Spec A).residueField (specPolynomialBase ζ))) :
    fibreGenericResidueFieldEquiv hζ (fibrePolynomialEval ζ g) =
      algebraMap _ (RatFunc ((Spec A).residueField (specPolynomialBase ζ))) g := by
  let _ := fibrePolynomialAlgebra ζ
  have := isFractionRing_fibrePolynomialAlgebra hζ
  exact (IsLocalization.algEquiv
    (nonZeroDivisors (Polynomial ((Spec A).residueField (specPolynomialBase ζ))))
    ((Spec (CommRingCat.of (Polynomial A))).residueField ζ)
    (RatFunc ((Spec A).residueField (specPolynomialBase ζ)))).commutes g

/-- On the value at `ζ` of a polynomial over `A`, the identification is the image of the
polynomial in `κ(f ζ)[T]`. -/
theorem fibreGenericResidueFieldEquiv_specEval (hζ : IsGenericFibrePoint ζ) (h : Polynomial A) :
    fibreGenericResidueFieldEquiv hζ (specEval ζ h) =
      algebraMap _ (RatFunc ((Spec A).residueField (specPolynomialBase ζ)))
        (mapRingHom (specEval (specPolynomialBase ζ)) h) := by
  rw [← fibrePolynomialEval_mapRingHom, fibreGenericResidueFieldEquiv_fibrePolynomialEval]

/-- On `κ(f ζ)`, the identification is the inclusion of the constants. -/
theorem fibreGenericResidueFieldEquiv_residueFieldMap (hζ : IsGenericFibrePoint ζ)
    (c : (Spec A).residueField (specPolynomialBase ζ)) :
    fibreGenericResidueFieldEquiv hζ
        ((Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).residueFieldMap ζ c) =
      algebraMap _ (RatFunc ((Spec A).residueField (specPolynomialBase ζ))) c := by
  have : (Spec.map (CommRingCat.ofHom (C : A →+* Polynomial A))).residueFieldMap ζ c =
      fibrePolynomialEval ζ (C c) := by
    rw [fibrePolynomialEval, coe_eval₂RingHom, eval₂_C]
  rw [this, fibreGenericResidueFieldEquiv_fibrePolynomialEval, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

/-! ### The local ring of `closure {ζ}` at a point of the fibre -/

/-- The prime of a point of `closure {ζ}`, read as a point of `Spec A[T]`. -/
theorem asIdeal_subschemeι_pointClosurePoint {w : Spec (CommRingCat.of (Polynomial A))}
    (h : w ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A))))) :
    ((integralComponentAt ζ).subschemeι (pointClosurePoint ζ h)).asIdeal = w.asIdeal := by
  rw [subschemeι_pointClosurePoint]

/-- The germs of polynomials over `A` in the local ring of `closure {ζ}` at `w`. -/
def closureStalkGerm (ζ : Spec (CommRingCat.of (Polynomial A)))
    {w : Spec (CommRingCat.of (Polynomial A))}
    (h : w ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A))))) :
    Polynomial A →+* (integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h) :=
  ((integralComponentAt ζ).subschemeι.stalkMap (pointClosurePoint ζ h)).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv ≫
      (Spec (CommRingCat.of (Polynomial A))).presheaf.germ ⊤
        ((integralComponentAt ζ).subschemeι (pointClosurePoint ζ h)) trivial).hom

variable {w : Spec (CommRingCat.of (Polynomial A))}
  (h : w ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A)))))

/-- The germ of `b` in the local ring of `closure {ζ}` at `w` is a unit exactly when `b` does not
vanish at `w`. -/
theorem isUnit_closureStalkGerm_iff (b : Polynomial A) :
    IsUnit (closureStalkGerm ζ h b) ↔ b ∉ w.asIdeal := by
  rw [← asIdeal_subschemeι_pointClosurePoint h, ← isUnit_germ_ΓSpecIso_inv_iff]
  exact isUnit_map_iff ((integralComponentAt ζ).subschemeι.stalkMap (pointClosurePoint ζ h)).hom
    (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv ≫
      (Spec (CommRingCat.of (Polynomial A))).presheaf.germ ⊤
        ((integralComponentAt ζ).subschemeι (pointClosurePoint ζ h)) trivial) b)

/-- Every element of the local ring of `closure {ζ}` at `w` is a fraction of germs of polynomials,
with denominator not vanishing at `w`. -/
theorem exists_mul_closureStalkGerm_eq
    (z : (integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h)) :
    ∃ a b, b ∉ w.asIdeal ∧ z * closureStalkGerm ζ h b = closureStalkGerm ζ h a := by
  obtain ⟨z', rfl⟩ :=
    (integralComponentAt ζ).subschemeι.stalkMap_surjective (pointClosurePoint ζ h) z
  obtain ⟨a, b, hb, hab⟩ := exists_mul_germ_ΓSpecIso_inv_eq _ z'
  refine ⟨a, b, by rwa [← asIdeal_subschemeι_pointClosurePoint h], ?_⟩
  simp only [closureStalkGerm, RingHom.comp_apply, ← map_mul, hab]

/-- The local ring of `closure {ζ}` at `w`, mapped to `κ(ζ)` through the function field of
`closure {ζ}`. -/
def closureStalkToResidueField :
    (integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h) →+*
      (Spec (CommRingCat.of (Polynomial A))).residueField ζ :=
  (pointClosureFunctionFieldEquiv ζ).toRingHom.comp
    (algebraMap _ (integralComponentAt ζ).subscheme.functionField)

/-- The map `closureStalkToResidueField h` sends a germ to its image in the function field of
`closure {ζ}`, identified with `κ(ζ)`. -/
theorem closureStalkToResidueField_apply
    (s : (integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h)) :
    closureStalkToResidueField h s =
      pointClosureFunctionFieldEquiv ζ
        (algebraMap _ (integralComponentAt ζ).subscheme.functionField s) := rfl

/-- The map from the local ring of `closure {ζ}` at `w` to `κ(ζ)` is injective. -/
theorem closureStalkToResidueField_injective :
    Function.Injective (closureStalkToResidueField h) :=
  (pointClosureFunctionFieldEquiv ζ).injective.comp
    (IsFractionRing.injective _ (integralComponentAt ζ).subscheme.functionField)

/-- The germ of a polynomial, read in `κ(ζ)`, is its value at `ζ`. -/
theorem closureStalkToResidueField_closureStalkGerm (a : Polynomial A) :
    closureStalkToResidueField h (closureStalkGerm ζ h a) = specEval ζ a := by
  have hspec : ζ ⤳ (integralComponentAt ζ).subschemeι (pointClosurePoint ζ h) := by
    rw [subschemeι_pointClosurePoint]
    exact specializes_iff_mem_closure.mpr h
  rw [closureStalkToResidueField_apply, closureStalkGerm, RingHom.comp_apply,
    pointClosureFunctionFieldEquiv_algebraMap_stalkMap ζ _ hspec]
  change (Spec (CommRingCat.of (Polynomial A))).residue ζ
      ((Spec (CommRingCat.of (Polynomial A))).presheaf.stalkSpecializes hspec
        ((Spec (CommRingCat.of (Polynomial A))).presheaf.germ ⊤ _ trivial
          ((Scheme.ΓSpecIso _).inv a))) = _
  exact congrArg (fun t ↦ (Spec (CommRingCat.of (Polynomial A))).residue ζ t)
    (TopCat.Presheaf.germ_stalkSpecializes_apply (Spec (CommRingCat.of (Polynomial A))).presheaf
      (U := ⊤) (y := (integralComponentAt ζ).subschemeι (pointClosurePoint ζ h)) trivial hspec _)

/-- The image in `κ(ζ)` of the local ring of `closure {ζ}` at `w` consists of the fractions of
values of polynomials with denominator not vanishing at `w`. -/
theorem mem_range_closureStalkToResidueField_iff
    (z : (Spec (CommRingCat.of (Polynomial A))).residueField ζ) :
    z ∈ (closureStalkToResidueField h).range ↔
      ∃ a b, b ∉ w.asIdeal ∧ z * specEval ζ b = specEval ζ a := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, b, hb, hab⟩ := exists_mul_closureStalkGerm_eq h s
    refine ⟨a, b, hb, ?_⟩
    rw [← closureStalkToResidueField_closureStalkGerm h,
      ← closureStalkToResidueField_closureStalkGerm h,
      ← map_mul, hab]
  · rintro ⟨a, b, hb, hab⟩
    obtain ⟨u, hu⟩ := (isUnit_closureStalkGerm_iff h b).mpr hb
    refine ⟨closureStalkGerm ζ h a * ↑u⁻¹, ?_⟩
    have hub : closureStalkToResidueField h (u : _) *
        closureStalkToResidueField h (↑u⁻¹ : _) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [map_mul, closureStalkToResidueField_closureStalkGerm, ← hab, mul_assoc,
      ← closureStalkToResidueField_closureStalkGerm h b, ← hu, hub, mul_one]

attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial in
/-- **The local ring of `closure {ζ}` at a point `w` of the fibre is the local ring of the affine
line over `κ(f ζ)` at the corresponding prime, compatibly with the identification of `κ(ζ)` with
`κ(f ζ)(T)`.** -/
theorem exists_closureStalk_ringEquiv (hζ : IsGenericFibrePoint ζ)
    (P : Ideal (Polynomial ((Spec A).residueField (specPolynomialBase ζ)))) [P.IsPrime]
    (hP : P.comap (mapRingHom (specEval (specPolynomialBase ζ))) = w.asIdeal) :
    ∃ ε : (integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h) ≃+*
        Localization.AtPrime P,
      ∀ s, algebraMap (Localization.AtPrime P)
          (RatFunc ((Spec A).residueField (specPolynomialBase ζ)))
          (ε s) = fibreGenericResidueFieldEquiv hζ (closureStalkToResidueField h s) := by
  refine exists_ringEquiv_of_mem_range_iff _ _ (closureStalkToResidueField_injective h)
    (IsFractionRing.injective (Localization.AtPrime P) _) _ fun z ↦ ?_
  rw [mem_range_closureStalkToResidueField_iff, mem_range_algebraMap_localizationAtPrime_iff,
    ← exists_mul_eq_iff_of_comap_eq (specEval (specPolynomialBase ζ)) (specEval_eq_zero_iff _)
      (exists_mul_specEval_eq _) _ hP]
  refine exists_congr fun a ↦ exists_congr fun b ↦ and_congr_right fun _ ↦ ?_
  rw [← fibreGenericResidueFieldEquiv_specEval hζ, ← fibreGenericResidueFieldEquiv_specEval hζ,
    ← map_mul]
  exact (fibreGenericResidueFieldEquiv hζ).injective.eq_iff.symm

/-! ### The closed points of the fibre -/

/-- The prime of `κ(f ζ)[T]` attached to a point `w` of the fibre through `ζ`: the extension of
the prime of `w`. -/
def fibrePrime (ζ w : Spec (CommRingCat.of (Polynomial A))) :
    Ideal (Polynomial ((Spec A).residueField (specPolynomialBase ζ))) :=
  w.asIdeal.map (mapRingHom (specEval (specPolynomialBase ζ)))

omit h in
/-- If `w` lies over the same point of `Spec A` as `ζ`, then the contraction of the prime of `w`
to `A` is the prime of that point. -/
theorem comap_C_asIdeal_of_specPolynomialBase_eq
    (hw : specPolynomialBase w = specPolynomialBase ζ) :
    w.asIdeal.comap (C : A →+* Polynomial A) = (specPolynomialBase ζ).asIdeal := by
  rw [← hw]
  rfl

omit h in
/-- For a point `w` of the fibre through `ζ`, the ideal `fibrePrime ζ w` is prime. -/
theorem isPrime_fibrePrime (hw : specPolynomialBase w = specPolynomialBase ζ) :
    (fibrePrime ζ w).IsPrime := by
  have : w.asIdeal.IsPrime := w.isPrime
  exact isPrime_map_mapRingHom _ (specEval_eq_zero_iff _) (exists_mul_specEval_eq _)
    (comap_C_asIdeal_of_specPolynomialBase_eq hw)

omit h in
/-- For a point `w` of the fibre through `ζ`, the contraction of `fibrePrime ζ w` to `A[T]` is the
prime of `w`. -/
theorem comap_fibrePrime (hw : specPolynomialBase w = specPolynomialBase ζ) :
    (fibrePrime ζ w).comap (mapRingHom (specEval (specPolynomialBase ζ))) = w.asIdeal := by
  have : w.asIdeal.IsPrime := w.isPrime
  exact comap_map_mapRingHom _ (specEval_eq_zero_iff _) (exists_mul_specEval_eq _)
    (comap_C_asIdeal_of_specPolynomialBase_eq hw)

omit h in
/-- Only the generic point of the fibre has the zero ideal attached. -/
theorem fibrePrime_ne_bot (hζ : IsGenericFibrePoint ζ)
    (hw : specPolynomialBase w = specPolynomialBase ζ)
    (hne : w ≠ ζ) : fibrePrime ζ w ≠ ⊥ := by
  intro hbot
  refine hne (PrimeSpectrum.ext ?_)
  rw [← comap_fibrePrime hw, hbot, hζ]
  ext b
  rw [Ideal.mem_comap, Ideal.mem_bot, mapRingHom_eq_zero_iff _ (specEval_eq_zero_iff _)]

omit h in
/-- The other points of the fibre are closed points of the affine line over `κ(f ζ)`. -/
theorem isMaximal_fibrePrime (hζ : IsGenericFibrePoint ζ)
    (hw : specPolynomialBase w = specPolynomialBase ζ)
    (hne : w ≠ ζ) : (fibrePrime ζ w).IsMaximal := by
  have := isPrime_fibrePrime hw
  exact IsPrime.to_maximal_ideal (fibrePrime_ne_bot hζ hw hne)

omit h in
/-- Points of the fibre with the same attached prime are equal. -/
theorem eq_of_fibrePrime_eq {w' : Spec (CommRingCat.of (Polynomial A))}
    (hw : specPolynomialBase w = specPolynomialBase ζ)
    (hw' : specPolynomialBase w' = specPolynomialBase ζ)
    (heq : fibrePrime ζ w = fibrePrime ζ w') : w = w' :=
  PrimeSpectrum.ext (by rw [← comap_fibrePrime hw, heq, comap_fibrePrime hw'])

omit h in
/-- Every closed point of the affine line over `κ(f ζ)` is attached to a point of the fibre. -/
theorem exists_fibrePrime_eq (P : Ideal (Polynomial ((Spec A).residueField (specPolynomialBase ζ))))
    [P.IsPrime] :
    ∃ w : Spec (CommRingCat.of (Polynomial A)),
      specPolynomialBase w = specPolynomialBase ζ ∧ fibrePrime ζ w = P := by
  refine ⟨⟨P.comap (mapRingHom (specEval (specPolynomialBase ζ))), Ideal.comap_isPrime _ _⟩, ?_, ?_⟩
  · exact PrimeSpectrum.ext (comap_C_comap_mapRingHom _ (specEval_eq_zero_iff _)
      ‹P.IsPrime›.ne_top)
  · exact map_comap_mapRingHom _ (specEval_eq_zero_iff _) (exists_mul_specEval_eq _) P

/-- **The local ring of `closure {ζ}` at a point `w ≠ ζ` of the fibre is a discrete valuation
ring**: it is the local ring of the affine line over a field at a closed point. -/
theorem isDiscreteValuationRing_closureStalk (hζ : IsGenericFibrePoint ζ)
    (hw : specPolynomialBase w = specPolynomialBase ζ) (hne : w ≠ ζ) :
    IsDiscreteValuationRing
      ((integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h)) := by
  have := isMaximal_fibrePrime hζ hw hne
  have := isDiscreteValuationRing_localizationAtPrime_polynomial (fibrePrime ζ w)
  obtain ⟨ε, -⟩ := exists_closureStalk_ringEquiv h hζ (fibrePrime ζ w) (comap_fibrePrime hw)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ε.symm

omit h in
/-- The generic point of a fibre specializes to every point of that fibre. -/
theorem IsGenericFibrePoint.specializes (hζ : IsGenericFibrePoint ζ)
    (hw : specPolynomialBase w = specPolynomialBase ζ) : ζ ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes ζ w).mp ?_
  change ζ.asIdeal ≤ w.asIdeal
  rw [hζ, Ideal.map_le_iff_le_comap, comap_C_asIdeal_of_specPolynomialBase_eq hw]

/-- The generic point of a fibre has the zero ideal attached. -/
theorem fibrePrime_self (hζ : IsGenericFibrePoint ζ) : fibrePrime ζ ζ = ⊥ := by
  rw [fibrePrime, Ideal.map_eq_bot_iff_le_ker, hζ]
  intro b hb
  rwa [RingHom.mem_ker, mapRingHom_eq_zero_iff _ (specEval_eq_zero_iff _)]

attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial in
/-- **The order of vanishing along a closed point of the fibre, read on the affine line.** If a
unit of `κ(ζ)`, read as a rational function on `closure {ζ}`, has order zero at a point `w ≠ ζ`
of the fibre, then its image in `κ(f ζ)(T)` has trivial order at the closed point of the affine
line attached to `w`. -/
theorem ordFrac_fibreGenericResidueFieldEquiv_eq_one (hζ : IsGenericFibrePoint ζ)
    (hw : specPolynomialBase w = specPolynomialBase ζ) (hne : w ≠ ζ)
    [IsLocallyNoetherian (integralComponentAt ζ).subscheme]
    (u : ((Spec (CommRingCat.of (Polynomial A))).residueField ζ)ˣ)
    (hord : (integralComponentAt ζ).subscheme.ord ((pointClosureFunctionFieldEquiv ζ).symm u)
      (pointClosurePoint ζ h) = 0) :
    haveI := isMaximal_fibrePrime hζ hw hne
    Ring.ordFrac (Localization.AtPrime (fibrePrime ζ w))
      (fibreGenericResidueFieldEquiv hζ u) = 1 := by
  have := isMaximal_fibrePrime hζ hw hne
  have := isDiscreteValuationRing_closureStalk h hζ hw hne
  obtain ⟨ε, hε⟩ := exists_closureStalk_ringEquiv h hζ (fibrePrime ζ w) (comap_fibrePrime hw)
  have hcoh : Order.coheight (pointClosurePoint ζ h) = 1 := by
    have := ringKrullDim_stalk_eq_coheight (pointClosurePoint ζ h)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at this
    exact_mod_cast this.symm
  set f := (pointClosureFunctionFieldEquiv ζ).symm (u : _) with hf
  have hne0 : Ring.ordFrac ((integralComponentAt ζ).subscheme.presheaf.stalk
      (pointClosurePoint ζ h)) f ≠ 0 :=
    (_root_.map_ne_zero _).mpr ((_root_.map_ne_zero _).mpr u.ne_zero)
  have h1 := ord_eq_toAdd_unzero_ordFrac hcoh hne0
  rw [hord] at h1
  have h2 : Ring.ordFrac ((integralComponentAt ζ).subscheme.presheaf.stalk
      (pointClosurePoint ζ h)) f = 1 := by
    rw [← WithZero.coe_unzero hne0, ← WithZero.coe_one]
    congr 1
    rw [← ofAdd_toAdd (WithZero.unzero hne0), ← h1, ofAdd_zero]
  have h3 := ordFrac_ringEquiv ε ((pointClosureFunctionFieldEquiv ζ).trans
    (fibreGenericResidueFieldEquiv hζ)) (fun r ↦ (hε r).symm) f
  rw [h2] at h3
  rw [← h3, RingEquiv.trans_apply, hf, RingEquiv.apply_symm_apply]

end Fibre

end Stacks.Chow

end
