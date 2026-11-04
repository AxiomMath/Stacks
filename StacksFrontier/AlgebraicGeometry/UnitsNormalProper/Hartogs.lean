module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Algebraic Hartogs for a normal scheme

Let `X` be a normal integral locally Noetherian scheme.  This file proves that an element of
`X.functionField` whose order of vanishing `AlgebraicGeometry.Scheme.ord` is zero at every point
of codimension one is the image of a global section of the structure sheaf: the scheme-level form
of algebraic Hartogs.

## Main results

* `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one`:
  the ring form.  An element of the fraction field of a Noetherian normal domain whose
  denominator can be chosen outside every height-one prime lies in the ring.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk`:  the local ring at
  a codimension-one point of a normal integral locally Noetherian scheme is a discrete
  valuation ring.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero`:  at such a point,
  an element of the function field of order of vanishing zero is the image of a *unit* of the
  local ring.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_section_of_forall_ord_eq_zero`:  the
  conclusion over a nonempty affine open.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalSection_of_forall_ord_eq_zero`:  the
  global conclusion.
* `Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero`:  a unit
  of the function field of order of vanishing zero at every codimension-one point is the germ of
  an invertible global section.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Order

universe u

namespace Stacks.AlgebraicGeometry.UnitsNormalProper

/-- **Algebraic Hartogs, ring form.** An element of the fraction field of a Noetherian normal
domain whose denominator can be chosen outside every height-one prime lies in the ring. -/
theorem exists_algebraMap_eq_of_forall_height_eq_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {z : K}
    (hz : ∀ q : PrimeSpectrum R, q.asIdeal.height = 1 →
      ∃ a s : R, s ∉ q.asIdeal ∧ z * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = z := by
  have hbot := (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    (R := R) K).2.1
  have hmem : z ∈ (⊥ : Subalgebra R K) := by
    rw [← hbot]
    refine Algebra.mem_iInf.mpr fun q => Algebra.mem_iInf.mpr fun hq => ?_
    obtain ⟨a, s, hs, hzas⟩ := hz q hq
    have hs0 : algebraMap R K s ≠ 0 := by
      simpa using fun h : s = 0 => hs (h ▸ q.asIdeal.zero_mem)
    exact ⟨a, s, hs, by rw [← hzas, mul_assoc, mul_inv_cancel₀ hs0, mul_one]⟩
  exact Algebra.mem_bot.mp hmem

/-- The local ring of a normal integral locally Noetherian scheme at a point of codimension one
is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsNormal X] {x : X} (hx : coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hx]; rfl
  have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance,
      AlgebraicGeometry.IsNormal.stalk_normal x, hdim⟩
  have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
    ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
  exact h1.choose_spec

/-- At a codimension-one point of a normal integral locally Noetherian scheme, an element of the
function field of order of vanishing zero is the image of a unit of the local ring. -/
theorem exists_isUnit_of_ord_eq_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsNormal X] {x : X} (hx : coheight x = 1) {z : X.functionField}
    (hz : z ≠ 0) (h0 : Scheme.ord z x = 0) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      algebraMap (X.presheaf.stalk x) X.functionField a = z := by
  have hdvr := isDiscreteValuationRing_stalk (X := X) hx
  have hord : Scheme.ordHom x hx z = (Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) :=
    (Scheme.ord_eq_iff hx hz).mp h0
  have hfrac : Ring.ordFrac (X.presheaf.stalk x) z = 1 := by
    have : Scheme.ordHom x hx = Ring.ordFrac (X.presheaf.stalk x) := rfl
    rw [← this, hord]; simp
  have hkey := Ring.mker_ordFrac_eq_isUnitSubmonoid (R := X.presheaf.stalk x)
    (K := X.functionField)
  have hmem : z ∈ (IsUnit.submonoid (X.presheaf.stalk x)).map
      (algebraMap (X.presheaf.stalk x) X.functionField) := by
    rw [← hkey]; exact hfrac
  exact hmem

/-- **Algebraic Hartogs on an affine open.** On a normal integral locally Noetherian scheme, an
element of the function field whose order of vanishing is zero at every codimension-one point is
a section over every nonempty affine open. -/
theorem exists_section_of_forall_ord_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNormal X] (U : X.affineOpens) [Nonempty U.1]
    {z : X.functionField} (hz : z ≠ 0)
    (h0 : ∀ y : X, coheight y = 1 → Scheme.ord z y = 0) :
    ∃ r : Γ(X, U.1), algebraMap Γ(X, U.1) X.functionField r = z := by
  have hU : IsAffineOpen U.1 := U.2
  have : IsDomain Γ(X, U.1) := AlgebraicGeometry.IsIntegral.component_integral U.1
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsIntegrallyClosed Γ(X, U.1) :=
    (AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal X).mp inferInstance U inferInstance
  have : IsFractionRing Γ(X, U.1) X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U.1 hU
  refine exists_algebraMap_eq_of_forall_height_eq_one X.functionField fun q hq => ?_
  let q' : ↥(Spec Γ(X, U.1)) := q
  have hround : hU.isoSpec.hom.base (hU.isoSpec.inv.base q') = q := by
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  obtain ⟨u, hpq⟩ : ∃ u : U.1, hU.primeIdealOf u = q := ⟨hU.isoSpec.inv.base q', hround⟩
  have hch : coheight (u : X) = 1 := by
    rw [show (u : X) = U.1.ι.base u from rfl,
      AlgebraicGeometry.coheight_eq_of_isOpenImmersion U.1.ι (x := u),
      ← AlgebraicGeometry.coheight_eq_of_isOpenImmersion hU.isoSpec.hom (x := u),
      ← AlgebraicGeometry.idealHeight_eq_coheight, show hU.isoSpec.hom.base u = q from hpq]
    exact hq
  obtain ⟨a, -, hae⟩ := exists_isUnit_of_ord_eq_zero hch hz (h0 _ hch)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (u : X)) q.asIdeal := by
    rw [← hpq]; exact hU.isLocalization_stalk u
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl a
  refine ⟨b, s.1, s.2, ?_⟩
  have hbs' : IsLocalization.mk' (X.presheaf.stalk (u : X)) b s = a := hbs
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (u : X)) b s
  rw [hbs'] at hspec
  have hcg := congrArg (algebraMap (X.presheaf.stalk (u : X)) X.functionField) hspec
  rw [map_mul, hae] at hcg
  rwa [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk (u : X)) X.functionField s.1,
    IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk (u : X)) X.functionField b]

/-- **Algebraic Hartogs.** On a normal integral locally Noetherian scheme, an element of the
function field whose order of vanishing is zero at every codimension-one point is the image of a
global section. -/
theorem exists_globalSection_of_forall_ord_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNormal X] {z : X.functionField} (hz : z ≠ 0)
    (h0 : ∀ y : X, coheight y = 1 → Scheme.ord z y = 0) :
    ∃ a : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial a = z := by
  classical
  have hgen (V : X.Opens) (hV : Nonempty V) : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hpick : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 := fun x => by
    obtain ⟨V, hV, hxV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (x := x) (U := ⊤) trivial
    exact ⟨⟨V, hV⟩, hxV⟩
  choose V hxV using hpick
  have hne (x : X) : Nonempty ((V x).1) := ⟨⟨x, hxV x⟩⟩
  have hsec : ∀ x : X, ∃ r : Γ(X, (V x).1), X.germToFunctionField (V x).1 r = z := fun x =>
    have := hne x
    exists_section_of_forall_ord_eq_zero (V x) hz h0
  choose s hs using hsec
  let U : X → X.Opens := fun x => (V x).1
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro x y
    have hx := hne x
    have hy := hne y
    have : Nonempty (U x ⊓ U y : X.Opens) := ⟨⟨genericPoint X, hgen _ hx, hgen _ hy⟩⟩
    apply X.germToFunctionField_injective (U x ⊓ U y : X.Opens)
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hs x).trans (hs y).symm
  obtain ⟨t, ht, -⟩ :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
      (by intro x _; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) s hcompat
  refine ⟨t, ?_⟩
  let x : X := (inferInstance : Nonempty X).some
  exact (X.presheaf.germ_res_apply (homOfLE (le_top : U x ≤ ⊤)) (genericPoint X)
    (hgen _ (hne x)) t).symm.trans ((congrArg _ (ht x)).trans (hs x))

/-- **Algebraic Hartogs for units.** On a normal integral locally Noetherian scheme, a unit of
the function field whose order of vanishing is zero at every codimension-one point is the germ at
the generic point of an *invertible* global section. -/
theorem exists_globalUnit_of_forall_ord_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNormal X] (z : X.functionFieldˣ)
    (h0 : ∀ y : X, coheight y = 1 → Scheme.ord (z : X.functionField) y = 0) :
    ∃ s : (Γ(X, ⊤))ˣ,
      X.presheaf.germ ⊤ (genericPoint X) trivial (s : Γ(X, ⊤)) = (z : X.functionField) := by
  have hone : ∀ y : X, Scheme.ord (1 : X.functionField) y = 0 := fun y => by
    have h := Scheme.ord_mul (x := y) (f := (1 : X.functionField)) (g := 1)
      one_ne_zero one_ne_zero
    rw [one_mul] at h
    omega
  have hinv : ∀ y : X, coheight y = 1 →
      Scheme.ord ((z⁻¹ : X.functionFieldˣ) : X.functionField) y = 0 := fun y hy => by
    have h := Scheme.ord_mul (x := y) (f := (z : X.functionField))
      (g := ((z⁻¹ : X.functionFieldˣ) : X.functionField)) z.ne_zero z⁻¹.ne_zero
    rw [show (z : X.functionField) * ((z⁻¹ : X.functionFieldˣ) : X.functionField) = 1 from
      z.mul_inv, hone y, h0 y hy] at h
    omega
  obtain ⟨a, ha⟩ := exists_globalSection_of_forall_ord_eq_zero z.ne_zero h0
  obtain ⟨b, hb⟩ := exists_globalSection_of_forall_ord_eq_zero z⁻¹.ne_zero hinv
  have hab : a * b = 1 := by
    refine germ_injective_of_isIntegral (X := X) (U := (⊤ : X.Opens)) (genericPoint X) trivial ?_
    rw [map_mul, map_one, ha, hb, z.mul_inv]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Stacks.AlgebraicGeometry.UnitsNormalProper
