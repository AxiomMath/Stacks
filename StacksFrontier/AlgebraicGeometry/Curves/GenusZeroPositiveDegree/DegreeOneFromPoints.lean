module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

/-!
# An invertible module of degree one from normal closed points of coprime degrees

Let `X` be a proper curve over a field `k` and let `x₁, …, xₙ` be closed points of `X` whose local
rings are normal and whose residue degrees `[κ(xᵢ) : k]` have greatest common divisor `1`. Then
`X` carries an invertible module of degree `1`. This is the step "(8) ⟹ (7)" in the proof of
[Stacks, Tag 0C6U].

A closed point with a normal local ring is an effective Cartier divisor `Dₓ`
([Stacks, Tag 0B8Y]), and the invertible module `𝒪_X(Dₓ)` has a regular section, the canonical
section, whose zero scheme is the reduced point; so its degree is `dim_k Γ({x}, 𝒪) = [κ(x) : k]`
([Stacks, Tag 0B40] read through the zero scheme). The degrees of invertible modules form a
subgroup of `ℤ` (degree is additive in tensor products and negated by inverses,
[Stacks, Tag 0AYX]), so it contains `gcd [κ(xᵢ) : k] = 1`.

## Main results

* `AlgebraicGeometry.finrank_globalSections_vanishingIdeal_singleton`: the reduced closed point
  `{x}` has `dim_k Γ({x}, 𝒪) = [κ(x) : k]`.
* `AlgebraicGeometry.invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton`:
  `deg 𝒪_X(x) = [κ(x) : k]` for a closed point which is an effective Cartier divisor.
* `AlgebraicGeometry.exists_invertibleCurveDegree_eq_one_of_gcd`: the degree-one invertible
  module.

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The reduced closed point `{x}` has `dim_k Γ({x}, 𝒪) = [κ(x) : k]`.** The reduced closed
subscheme on a closed point is integral with a single point, so its global sections are its
residue field there, which the closed immersion identifies with `κ(x)`. Both `k`-structures
come from the structure morphism. -/
theorem finrank_globalSections_vanishingIdeal_singleton {x : X} (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).subscheme,
        ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫
          ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).subschemeι ≫
            f).appTop).hom.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.finrank k Γ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).subscheme,
        ⊤) = Module.finrank k (X.residueField x) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hIdef
  set ι := I.subschemeι with hιdef
  have hcl : (⟨{x}, hx⟩ : Closeds X) = Closeds.closure ({x} : Set X) :=
    Closeds.ext hx.closure_eq.symm
  have : IsIntegral I.subscheme := by
    rw [hIdef, hcl]
    infer_instance
  have hrange : Set.range ι = {x} := by
    rw [hιdef, Scheme.IdealSheafData.range_subschemeι, hIdef,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : Subsingleton I.subscheme := ⟨fun a b => by
    have ha : ι a ∈ Set.range ι := ⟨a, rfl⟩
    have hb : ι b ∈ Set.range ι := ⟨b, rfl⟩
    rw [hrange] at ha hb
    exact ι.isClosedEmbedding.injective (ha.trans hb.symm)⟩
  obtain ⟨z, hz⟩ : x ∈ Set.range ι := hrange ▸ rfl
  have : IsIso (I.subscheme.Γevaluation z) :=
    Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton z
  let algΓ : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (ι ≫ f).appTop).hom.toAlgebra
  let algZ : Algebra k (I.subscheme.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (ι ≫ f).appTop ≫ I.subscheme.Γevaluation z).hom.toAlgebra
  -- `Γ(Z, 𝒪) ≅ κ(z)`, `k`-linearly
  have h1 : Module.finrank k Γ(I.subscheme, ⊤) =
      Module.finrank k (I.subscheme.residueField z) := by
    let e : Γ(I.subscheme, ⊤) ≃ₐ[k] I.subscheme.residueField z :=
      AlgEquiv.ofRingEquiv (f := (asIso (I.subscheme.Γevaluation z)).commRingCatIsoToRingEquiv)
        fun _ => rfl
    exact e.toLinearEquiv.finrank_eq
  -- `κ(x) ≅ κ(z)` along the closed immersion, `k`-linearly
  have key : ∀ (y : X) (hy : ι z = y),
      let : Algebra k (X.residueField y) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation y).hom.toAlgebra
      Module.finrank k (X.residueField y) = Module.finrank k (I.subscheme.residueField z) := by
    rintro y rfl
    let : Algebra k (X.residueField (ι z)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (ι z)).hom.toAlgebra
    let e : X.residueField (ι z) ≃ₐ[k] I.subscheme.residueField z :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (ι.residueFieldMap z).hom
        (Stacks.Chow.bijective_residueFieldMap_of_isClosedImmersion ι z))
        fun c => by
          change (ι.residueFieldMap z).hom (X.Γevaluation (ι z)
              (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) =
            I.subscheme.Γevaluation z ((ι ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
          rw [Scheme.Γevaluation_naturality_apply, Scheme.Hom.comp_appTop]
          rfl
    exact e.toLinearEquiv.finrank_eq
  exact h1.trans (key x hz).symm

variable [IsCurve k f] [IsProper f]

/-- **`deg 𝒪_X(x) = [κ(x) : k]`** for a closed point `x` of a proper curve which is an effective
Cartier divisor: the canonical section of `𝒪_X(x)` is regular with zero scheme the reduced point
`{x}` ([Stacks, Tag 01X0]), so the degree is `dim_k H⁰({x}, 𝒪_X(x)|_{x}) = dim_k Γ({x}, 𝒪)`. -/
theorem invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : IsClosed ({x} : Set X))
    [Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))] :
    letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Stacks.Divisors.modulesInvertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) :=
      Stacks.Divisors.isInvertible_invertibleSheaf _
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    invertibleCurveDegree k f hdim (Stacks.Divisors.modulesInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) =
      Module.finrank k (X.residueField x) := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hDdef
  set L := Stacks.Divisors.modulesInvertibleSheaf D
  set s := Stacks.Divisors.canonicalSections D
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.Divisors.isInvertible_invertibleSheaf D
  -- the canonical section does not vanish identically: it is nonvanishing off `x`
  obtain ⟨y, hyx⟩ := Stacks.ProjectiveSpaceSections.exists_ne_of_isCurve f x
  have hs : s.eval (op ⊤) ≠ 0 := by
    refine eval_top_ne_zero_of_mem_nonvanishingLocus L s (x := y) ?_
    change y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (Stacks.Divisors.invertibleSheaf D) (Stacks.Divisors.canonicalSections D)
    rw [Stacks.Divisors.nonvanishingLocus_canonicalSections, hDdef,
      supportSet_vanishingIdeal_singleton hx]
    exact hyx
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k f hdim L s hs
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim L s hs
      (forall_finiteDimensional_cohomologyOverField_unit k f),
    finrank_cohomologyOverField_eq_of_iso k ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) e 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  have hz : zeroScheme X L (s.eval (op ⊤)) = D := Stacks.Divisors.zeroScheme_canonicalSections D
  have key : ∀ I : X.IdealSheafData, I = D →
      (let : Algebra k Γ(I.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(I.subscheme, ⊤)) =
      let : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.finrank k (X.residueField x) := by
    rintro I rfl
    exact finrank_globalSections_vanishingIdeal_singleton f hx
  exact_mod_cast key _ hz

/-- **The degrees of invertible modules on a proper curve form a subgroup of `ℤ`**: `𝒪_X` has
degree `0` and `deg(ℒ ⊗ 𝒩^{⊗ -1}) = deg ℒ - deg 𝒩` ([Stacks, Tag 0AYX]). -/
def invertibleCurveDegreeSubgroup (hdim : topologicalKrullDim X ≤ 1) : AddSubgroup ℤ :=
  have hsub : ∀ a b : ℤ,
      (∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        invertibleCurveDegree k f hdim L = a) →
      (∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        invertibleCurveDegree k f hdim L = b) →
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        invertibleCurveDegree k f hdim L = a - b := by
    rintro a b ⟨L, hL, rfl⟩ ⟨N, hN, rfl⟩
    exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj (tensorPowerModule N (-1)),
      isInvertible_tensorSheaf_tensorPowerModule_neg_one L N,
      invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one k f hdim N L⟩
  have hzero : ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f hdim L = 0 :=
    ⟨SheafOfModules.unit X.ringCatSheaf, Stacks.SheafOfModules.isInvertible_unit _ _,
      invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _ (Iso.refl _)⟩
  { carrier := {d | ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L), invertibleCurveDegree k f hdim L = d}
    zero_mem' := hzero
    add_mem' := fun {a b} ha hb => by
      simpa using hsub a (-b) ha (by simpa using hsub 0 b hzero hb)
    neg_mem' := fun {b} hb => by
      simpa using hsub 0 b hzero hb }

/-- **Normal closed points of coprime residue degrees give an invertible module of degree one.**
Let `X` be a proper curve over `k` and `x₁, …, xₙ` closed points with normal local rings and
`gcd [κ(xᵢ) : k] = 1`. Then some invertible `𝒪_X`-module has degree `1`.

Each `xᵢ` is an effective Cartier divisor ([Stacks, Tag 0B8Y]) with `deg 𝒪_X(xᵢ) = [κ(xᵢ) : k]`,
and the degrees of invertible modules form a subgroup of `ℤ`
(`AlgebraicGeometry.invertibleCurveDegreeSubgroup`), which therefore contains the greatest common
divisor `1`. -/
theorem exists_invertibleCurveDegree_eq_one_of_gcd (hdim : topologicalKrullDim X ≤ 1) {n : ℕ}
    (x : Fin n → X) (hx : ∀ i, IsClosed ({x i} : Set X))
    (hnorm : ∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i)))
    (hgcd : Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
      Module.finrank k (X.residueField (x i))) = 1) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f hdim L = 1 := by
  set d : Fin n → ℕ := fun i => let : Algebra k (X.residueField (x i)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
    Module.finrank k (X.residueField (x i)) with hd
  let H := invertibleCurveDegreeSubgroup f hdim
  have hmem : ∀ i, (d i : ℤ) ∈ H := by
    intro i
    have : Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x i}, hx i⟩ : Closeds X)) :=
      ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f (hx i)).out 2 4).mp
        (IsNormalRing.of_isIntegrallyClosed _)
    exact ⟨_, Stacks.Divisors.isInvertible_invertibleSheaf _,
      invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton f hdim (hx i)⟩
  let I : Ideal ℤ := AddSubgroup.toIntSubmodule H
  obtain ⟨g, hg⟩ := (inferInstance : I.IsPrincipal)
  have hdvd : ∀ i, g ∣ (d i : ℤ) := fun i => by
    have : (d i : ℤ) ∈ I := hmem i
    rwa [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at this
  have hnat : g.natAbs ∣ Finset.univ.gcd d :=
    Finset.dvd_gcd fun i _ => by simpa using Int.natAbs_dvd_natAbs.mpr (hdvd i)
  rw [hd, hgcd, Nat.dvd_one] at hnat
  have hone : (1 : ℤ) ∈ I := by
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact Int.natAbs_dvd.mp (by simp [hnat])
  exact hone

end AlgebraicGeometry

end
