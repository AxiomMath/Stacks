module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.TranscendenceDegree.FractionRing

/-!
# Residue fields of a scheme as residue fields of primes

Let `V` be an affine open of a scheme `X` containing a point `x`, and let `q` be the prime of
`Γ(X, V)` corresponding to `x`. The residue field `κ(x)` of the scheme at `x` is the residue
field `κ(q)` of that prime: the stalk `𝒪_{X, x}` is the localization of `Γ(X, V)` at `q`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and passing to residue fields of the
two local rings is an isomorphism. In particular `κ(x)` is a fraction field of `Γ(X, V) ⧸ q`.

That last statement is what lets the transcendence degree of a residue field extension of a
morphism of schemes be computed by the transcendence degree of an extension of quotients of
section rings, which is the shape in which the commutative algebra behind the dimension formula
(Stacks 02IJ) states it.

## Main results

* `AlgebraicGeometry.IsAffineOpen.residueFieldEquiv`: the isomorphism `κ(q) ≃ κ(x)`.
* `AlgebraicGeometry.IsAffineOpen.evaluation_eq_zero_iff_mem_primeIdealOf`: a section vanishes at
  `x` exactly when it lies in `q`.
* `AlgebraicGeometry.IsAffineOpen.isFractionRing_residueField`: `κ(x)` is a fraction field of
  `Γ(X, V) ⧸ q`.
* `AlgebraicGeometry.Scheme.Hom.evaluation_appLE_apply`: naturality of evaluation at a point for
  the restriction maps `appLE` of a morphism of schemes.
* `AlgebraicGeometry.trdeg_residueField_eq_trdeg_residueField_primeIdealOf`: the residue field
  extension `κ(x)/κ(f x)` of a morphism has the same transcendence degree as the residue field
  extension `κ(q)/κ(p)` of the corresponding primes.

## Implementation notes

The `Γ(X, V)`-algebra and `Γ(X, V) ⧸ q`-algebra structures on `κ(x)` are not instances, since
neither the open `V` nor the membership `x ∈ V` can be inferred; every statement that needs one
introduces it, the second one as the named `residueFieldQuotientAlgebra`.

The isomorphism `κ(q) ≃ κ(x)` is assembled from `IsLocalization.algEquiv`, which identifies the
stalk with `Localization.AtPrime q` as `Γ(X, V)`-algebras, and
`IsLocalRing.ResidueField.mapEquiv`. No transport along `IsAffineOpen.isoSpec` is involved.

## References

* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ V)

/-- On an affine open `V` containing `x`, the residue field of `X` at `x` is the residue field
of the prime of `Γ(X, V)` corresponding to `x`. -/
noncomputable def residueFieldEquiv :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField ≃+* X.residueField x :=
  letI := X.presheaf.algebra_section_stalk (U := V) ⟨x, hx⟩
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The isomorphism `κ(q) ≃ κ(x)` carries the image of a section of `X` over `V` to its value
at `x`. -/
@[simp]
lemma residueFieldEquiv_algebraMap (a : Γ(X, V)) :
    hV.residueFieldEquiv x hx (algebraMap Γ(X, V) _ a) = X.evaluation V x hx a := by
  let := X.presheaf.algebra_section_stalk (U := V) ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  rw [IsScalarTower.algebraMap_apply Γ(X, V)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField),
    IsLocalRing.ResidueField.algebraMap_eq]
  show IsLocalRing.residue _ ((IsLocalization.algEquiv
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
      (X.presheaf.stalk x)) (algebraMap _ _ a)) = _
  rw [AlgEquiv.commutes]
  rfl

/-- A section of `X` over an affine open `V ∋ x` vanishes at `x` exactly when it lies in the
prime of `Γ(X, V)` corresponding to `x`. -/
lemma evaluation_eq_zero_iff_mem_primeIdealOf (a : Γ(X, V)) :
    X.evaluation V x hx a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← hV.residueFieldEquiv_algebraMap x hx, map_eq_zero_iff _
    (hV.residueFieldEquiv x hx).injective, Ideal.algebraMap_residueField_eq_zero]

/-- The `Γ(X, V) ⧸ q`-algebra structure on `κ(x)` induced by evaluation at `x`, where `q` is the
prime of `Γ(X, V)` corresponding to `x`. -/
noncomputable abbrev residueFieldQuotientAlgebra :
    Algebra (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x) :=
  (Ideal.Quotient.lift _ (X.evaluation V x hx).hom
    fun a ha => (hV.evaluation_eq_zero_iff_mem_primeIdealOf x hx a).2 ha).toAlgebra

/-- The structure map `Γ(X, V) ⧸ q → κ(x)` is evaluation at `x`. -/
@[simp]
lemma algebraMap_residueFieldQuotientAlgebra_mk (a : Γ(X, V)) :
    letI := hV.residueFieldQuotientAlgebra x hx
    algebraMap (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x)
        (Ideal.Quotient.mk _ a) = X.evaluation V x hx a :=
  rfl

/-- The residue field `κ(x)` of a scheme at a point of an affine open `V` is a fraction field of
`Γ(X, V) ⧸ q`, for `q` the prime of `Γ(X, V)` corresponding to `x`. -/
theorem isFractionRing_residueField :
    letI := hV.residueFieldQuotientAlgebra x hx
    IsFractionRing (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x) := by
  let := hV.residueFieldQuotientAlgebra x hx
  refine IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := hV.residueFieldEquiv x hx) fun y => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.algebraMap_quotient_residueField_mk, hV.residueFieldEquiv_algebraMap,
    hV.algebraMap_residueFieldQuotientAlgebra_mk]

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Evaluation at a point is natural for the restriction maps of a morphism: for affine opens
`V ⊆ f⁻¹(U)` and `x ∈ V`, restricting a section of `Y` over `U` to `V` and evaluating at `x` is
the residue field map applied to its value at `f x`. -/
lemma Scheme.Hom.evaluation_appLE_apply (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (hfx : f x ∈ U) (a : Γ(Y, U)) :
    f.residueFieldMap x (Y.evaluation U (f x) hfx a) =
      X.evaluation V x hx (f.appLE U V hVU a) := by
  rw [Scheme.evaluation_naturality_apply]
  show IsLocalRing.residue _ (X.presheaf.germ (f ⁻¹ᵁ U) x hfx (f.app U a)) =
    IsLocalRing.residue _ (X.presheaf.germ V x hx (f.appLE U V hVU a))
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, X.presheaf.germ_res_apply]

/-- The residue field extension `κ(x)/κ(f x)` of a morphism of schemes has the same
transcendence degree as the residue field extension `κ(q)/κ(p)` of the primes corresponding to
`x` and `f x` on a pair of affine opens `V ⊆ f⁻¹(U)`. -/
theorem trdeg_residueField_eq_trdeg_residueField_primeIdealOf (f : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    haveI : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
    letI : Algebra (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.ResidueField
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField :=
      (Ideal.ResidueField.map _ _ (algebraMap Γ(Y, U) Γ(X, V)) Ideal.LiesOver.over).toAlgebra
    Algebra.trdeg (Y.residueField (f x)) (X.residueField x) =
      Algebra.trdeg (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.ResidueField
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let : Algebra (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.ResidueField
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ (algebraMap Γ(Y, U) Γ(X, V)) Ideal.LiesOver.over).toAlgebra
  rw [Algebra.trdeg_residueField_eq_trdeg_quotient]
  let := hU.residueFieldQuotientAlgebra (f x) (hVU hx)
  let := hV.residueFieldQuotientAlgebra x hx
  have := hU.isFractionRing_residueField (f x) (hVU hx)
  have := hV.isFractionRing_residueField x hx
  let : Algebra (Γ(Y, U) ⧸ (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal) (X.residueField x) :=
    ((algebraMap (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x)).comp
      (algebraMap (Γ(Y, U) ⧸ (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)
        (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal))).toAlgebra
  have : IsScalarTower (Γ(Y, U) ⧸ (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)
      (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x) := .of_algebraMap_eq' rfl
  have : IsScalarTower (Γ(Y, U) ⧸ (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)
      (Y.residueField (f x)) (X.residueField x) := by
    refine .of_algebraMap_eq fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    show algebraMap (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.residueField x)
      (algebraMap (Γ(Y, U) ⧸ (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal) _
        (Ideal.Quotient.mk _ a)) = _
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
      hV.algebraMap_residueFieldQuotientAlgebra_mk]
    show _ = f.residueFieldMap x (Y.evaluation U (f x) (hVU hx) a)
    rw [f.evaluation_appLE_apply hVU x hx (hVU hx) a]
    rfl
  exact Algebra.trdeg_eq_of_isFractionRing

end AlgebraicGeometry

end
