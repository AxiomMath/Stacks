module

public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitz
public import StacksFrontier.AlgebraicGeometry.Different.KaehlerDifferent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.KaehlerDifferent.DiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.RelativeDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.RingTheory.Kaehler.BaseChange

/-!
# The local multiplicities in the Riemann–Hurwitz formula

Let `f : X → Y` be a dominant morphism of smooth curves over a field `k`, let `R ⊆ X` be the
closed subscheme cut out by the (Kähler) different of `f`, and let `x ∈ X` be a closed point with
image `y`. The multiplicity of `x` in `R` is `d_x = length_{𝒪_{X,x}} 𝒪_{R,x}`. Then

1. `d_x = length_{𝒪_{X,x}}(Ω_{X/Y,x})`,
2. `d_x ≥ e_x - 1`, where `e_x` is the ramification index of `𝒪_{X,x}` over `𝒪_{Y,y}`,
3. `d_x = e_x - 1` if and only if `𝒪_{X,x}` is tamely ramified over `𝒪_{Y,y}`, that is,
   `κ(x) / κ(y)` is separable and the characteristic of `κ(y)` does not divide `e_x`.

## Main results

* `Stacks.Discriminant.map_fittingIdeal_kaehlerDifferential_localization`: the Kähler different
  commutes with localization.
* `AlgebraicGeometry.stalk_kaehlerDifferent_eq_fittingIdeal`: the stalk at `x` of the Kähler
  different of a morphism locally of finite type is the Kähler different of the stalk map.
* `AlgebraicGeometry.multiplicity_kaehlerDifferent_eq_length_stalk`,
  `AlgebraicGeometry.ramificationIdx_sub_one_le_multiplicity_kaehlerDifferent` and
  `AlgebraicGeometry.multiplicity_kaehlerDifferent_eq_iff`: parts (1), (2) and (3) of
  [Stacks, Tag 0C1F].

## Implementation notes

The different of `f` is taken to be its Kähler different, the zeroth Fitting ideal sheaf of
`Ω_{X/Y}`, which is the different of [Stacks, Tag 0BW4] for the quasi-finite syntomic morphism
`f` by [Stacks, Tag 0BWG]. The statements are made for a dominant morphism of smooth curves,
which every morphism satisfying the conditions of [Stacks, Tag 0C1C] is; properness and the
conditions on global sections of [Stacks, Tag 0C1D] are not needed for these local assertions.

At a closed point everything is read on the local rings: `𝒪_{X,x}` and `𝒪_{Y,y}` are discrete
valuation rings, the stalk map is injective because `f` is dominant, it is essentially of finite
type, and `κ(x) / κ(y)` is finite because `x` is closed. The stalk of the Kähler different is the
Kähler different of `𝒪_{X,x}` over `𝒪_{Y,y}`, and the three parts are the algebraic statements
`Stacks.Discriminant.length_quotient_fittingIdeal_zero_eq_length`,
`Stacks.Discriminant.ramificationIdx_sub_one_le_length_quotient_fittingIdeal` and
`Stacks.Discriminant.length_quotient_fittingIdeal_eq_iff`.

## References

* [Stacks Project, Tag 0C1F](https://stacks.math.columbia.edu/tag/0C1F)
* [Stacks Project, Tag 0BWG](https://stacks.math.columbia.edu/tag/0BWG)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Discriminant

/-- **The Kähler different commutes with localization.** Let `R₀ → S₀` be a ring map, `R` a
localization of `R₀` and `S` a localization of `S₀` which is an `R`-algebra compatibly. Then the
image in `S` of the Kähler different of `S₀` over `R₀` is the Kähler different of `S` over `R`:
`Ω_{S/R} = S ⊗_{S₀} Ω_{S₀/R₀}` and Fitting ideals commute with base change. -/
theorem map_fittingIdeal_kaehlerDifferential_localization {R₀ S₀ R S : Type u} [CommRing R₀]
    [CommRing S₀] [CommRing R] [CommRing S] [Algebra R₀ S₀] [Algebra R₀ R] [Algebra R S]
    [Algebra S₀ S] [Algebra R₀ S] [IsScalarTower R₀ S₀ S] [IsScalarTower R₀ R S]
    (M : Submonoid R₀) [IsLocalization M R] (N : Submonoid S₀) [IsLocalization N S]
    [Module.Finite S₀ Ω[S₀⁄R₀]] [Module.Finite S Ω[S⁄R]] :
    (fittingIdeal (R := S₀) (M := Ω[S₀⁄R₀]) 0).map (algebraMap S₀ S) =
      fittingIdeal (R := S) (M := Ω[S⁄R]) 0 := by
  have : Algebra.FormallyEtale S₀ S := Algebra.FormallyEtale.of_isLocalization N
  let e₁ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R₀ S₀ S
  let e₂ : Ω[S⁄R₀] ≃ₗ[S] Ω[S⁄R] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map R₀ R S S)
      (omega_localization_base R₀ S M R)
  have : Module.Finite S Ω[S⁄R₀] := Module.Finite.equiv e₂.symm
  have h1 := fittingIdeal_eq_of_linearEquiv (e₁.trans e₂) 0
  have h2 := (fittingIdeal_basic_properties.{u, u, u, u} (R := S₀) (M := Ω[S₀⁄R₀])).2.2.1 S 0
  rw [Nat.cast_zero] at h1 h2
  rw [← h2, h1]

end Stacks.Discriminant

namespace AlgebraicGeometry

open Stacks.Discriminant Stacks.DiscreteValuationRing.Ramification

/-- The algebra map induced by the stalk map of a morphism is a local homomorphism. -/
private theorem isLocalHom_algebraMap_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)

/-- The stalk map of a morphism locally of finite type is essentially of finite type. -/
theorem essFiniteType_stalkMap :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  let := (f.stalkMap x).hom.toAlgebra
  RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)

/-- **The stalk of the Kähler different is the Kähler different of the stalk map.** For a
morphism `f : X ⟶ Y` locally of finite type and `x ∈ X`, the ideal of `𝒪_{X,x}` induced by the
Kähler different of `f` is the zeroth Fitting ideal of `Ω_{𝒪_{X,x}/𝒪_{Y,f(x)}}`. -/
theorem stalk_kaehlerDifferent_eq_fittingIdeal :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := essFiniteType_stalkMap f x
    IdealSheafData.stalk (kaehlerDifferent f) x =
      _root_.fittingIdeal (R := X.presheaf.stalk x)
        (M := Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)]) 0 := by
  let := (f.stalkMap x).hom.toAlgebra
  have := essFiniteType_stalkMap f x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (V.2.preimage f.continuous)
  replace hUV : U ≤ f ⁻¹ᵁ V := hUV
  let := Stacks.Smooth.algebraAppLE f hUV
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (f x)) := (Y.presheaf.germ V (f x) hxV).hom.toAlgebra
  let : Algebra Γ(Y, V) (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (f.appLE V U hUV).hom).toAlgebra
  have hcompat : f.appLE V U hUV ≫ X.presheaf.germ U x hxU =
      Y.presheaf.germ V (f x) hxV ≫ f.stalkMap x := by
    ext a
    simp only [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply, X.presheaf.germ_res_apply]
  have : IsScalarTower Γ(Y, V) Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) a
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f x, hxV⟩
  have := moduleFinite_kaehlerDifferential_appLE f hU hV hUV
  rw [kaehlerDifferent_eq_fittingIdeal_relativeDifferentials,
    stalk_fittingIdeal_relativeDifferentials f 0 x ⟨U, hU⟩ hxU hV hUV]
  exact map_fittingIdeal_kaehlerDifferential_localization
    (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal.primeCompl (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl

end Stalk

section ClosedPoint

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X}

omit [LocallyOfFiniteType f] in
/-- The algebra structure on residue fields induced by the residue field map of a morphism is the
one induced by its stalk map. -/
theorem residueFieldMap_toAlgebra_eq :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    (f.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (ResidueField (Y.presheaf.stalk (f x)))
        (ResidueField (X.presheaf.stalk x))) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_algebraMap_stalkMap f x
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  rfl

end ClosedPoint

section Subscheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (R : X.IdealSheafData)

/-- The map of local rings of a closed subscheme sends the structure map `k → 𝒪_{X,x}` to that of
the closed subscheme. -/
theorem stalkMap_subschemeι_baseToStalk (z : R.subscheme) (c : k) :
    (R.subschemeι.stalkMap z).hom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (R.subschemeι z)
          (by simp)).hom c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (R.subschemeι ≫ p).appTop ≫
        R.subscheme.presheaf.germ ⊤ z (by simp)).hom c := by
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop]
  exact R.subschemeι.germ_stalkMap_apply ⊤ z (by simp) _

/-- **The degree of a closed subscheme finite over a field is the sum of its local
multiplicities.** If `R ⊆ X` is finite over `k` then
`dim_k Γ(R, 𝒪_R) = ∑_{x ∈ R} length_{𝒪_{X,x}}(𝒪_{X,x} / 𝓘_x) · [κ(x) : k]`, where `𝓘` is the
ideal sheaf of `R`. -/
theorem finrank_sections_subscheme_eq_finsum [IsFinite (R.subschemeι ≫ p)] :
    letI : Algebra k Γ(R.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (R.subschemeι ≫ p).appTop).hom.toAlgebra
    Module.finrank k Γ(R.subscheme, ⊤) =
      ∑ᶠ z : R.subscheme,
        letI : Algebra k (X.presheaf.stalk (R.subschemeι z)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
            X.presheaf.germ ⊤ (R.subschemeι z) (by simp)).hom.toAlgebra
        (Module.length (X.presheaf.stalk (R.subschemeι z))
            (X.presheaf.stalk (R.subschemeι z) ⧸
              IdealSheafData.stalk R (R.subschemeι z))).toNat *
          Module.finrank k (ResidueField (X.presheaf.stalk (R.subschemeι z))) := by
  rw [finrank_globalSections_eq_finsum_finrank_stalk k (R.subschemeι ≫ p)]
  refine finsum_congr fun z ↦ ?_
  rw [finrank_stalk_eq_length_mul_finrank_residueField k (R.subschemeι ≫ p) z]
  set x := R.subschemeι z
  let O := X.presheaf.stalk x
  let S := R.subscheme.presheaf.stalk z
  let φ : O →+* S := (R.subschemeι.stalkMap z).hom
  have hφ : Function.Surjective φ := R.subschemeι.stalkMap_surjective z
  let : Algebra k O := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
    X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  let : Algebra k S := ((Scheme.ΓSpecIso (.of k)).inv ≫ (R.subschemeι ≫ p).appTop ≫
    R.subscheme.presheaf.germ ⊤ z (by simp)).hom.toAlgebra
  let : Algebra O S := φ.toAlgebra
  have : IsLocalHom φ := inferInstanceAs (IsLocalHom (R.subschemeι.stalkMap z).hom)
  congr 1
  · -- the lengths
    congr 1
    rw [← Module.length_eq_of_surjective (S := O) (R := S) (M := S) hφ]
    let e : (O ⧸ RingHom.ker φ) ≃ₐ[O] S :=
      Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId O S) hφ
    rw [← e.toLinearEquiv.length_eq,
      (Submodule.quotEquivOfEq _ _ (IdealSheafData.ker_stalkMap_subschemeι R z)).length_eq]
  · -- the residue fields
    let ψ : ResidueField O →+* ResidueField S := ResidueField.map φ
    have hψ : Function.Bijective ψ := by
      refine ⟨ψ.injective, fun w ↦ ?_⟩
      obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective w
      obtain ⟨a, rfl⟩ := hφ b
      exact ⟨IsLocalRing.residue O a, rfl⟩
    let E : ResidueField O ≃ₗ[k] ResidueField S :=
      { toFun := ψ
        map_add' := ψ.map_add
        map_smul' := fun c a ↦ by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
          congr 1
          show ψ (IsLocalRing.residue O (algebraMap k O c)) =
            IsLocalRing.residue S (algebraMap k S c)
          exact congrArg (IsLocalRing.residue S) (stalkMap_subschemeι_baseToStalk p R z c)
        invFun := Function.surjInv hψ.2
        left_inv := Function.leftInverse_surjInv hψ
        right_inv := Function.rightInverse_surjInv hψ.2 }
    exact E.finrank_eq.symm

end Subscheme

section Curves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY]
  (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] {x : X}

omit [IsCurve k pY] [IsDominant f] in
include hf in
/-- A morphism of curves over `k` sends closed points to closed points. -/
theorem isClosed_map_of_isClosed (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f x} : Set Y) := by
  subst hf
  have := locallyOfFiniteType_of_comp f pY
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace pY
  exact f.closePoints_subset_preimage_closedPoints hx

include hf in
/-- **The local rings at a closed point of a dominant morphism of smooth curves.** Both are
discrete valuation rings, the stalk map is injective, and the residue field extension is
finite. -/
theorem localRings_of_isClosed (hx : IsClosed ({x} : Set X)) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    IsDiscreteValuationRing (X.presheaf.stalk x) ∧
      IsDiscreteValuationRing (Y.presheaf.stalk (f x)) ∧
      FaithfulSMul (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) ∧
      Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
        (ResidueField (X.presheaf.stalk x)) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_algebraMap_stalkMap f x
  have := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
  have hinj : ∀ z : X, Function.Injective (f.stalkMap z) :=
    ((tfae_isDominant_of_isIntegral f).out 1 6).mp ‹IsDominant f›
  refine ⟨IsCurve.isDiscreteValuationRing_stalk_of_isClosed k pX hx,
    IsCurve.isDiscreteValuationRing_stalk_of_isClosed k pY (isClosed_map_of_isClosed pX pY f hf hx),
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (hinj x), ?_⟩
  have h := finite_residueField_of_isClosed f hx
  rwa [residueFieldMap_toAlgebra_eq] at h

/-- **Stacks Project, Tag 0C1F, part (1).** Let `f : X → Y` be a dominant morphism of smooth
curves over a field and `x ∈ X` a closed point. The multiplicity `d_x = length_{𝒪_{X,x}} 𝒪_{R,x}`
of `x` in the closed subscheme `R` cut out by the different of `f` is the length of the stalk
`Ω_{X/Y,x}` of the sheaf of relative differentials. -/
@[stacks 0C1F "(1): `d_x = length_{𝒪_{X,x}}(Ω_{X/Y,x})`, for a dominant morphism of smooth curves;
the different is the Kähler different, which is the different of Tag 0BW4 by Tag 0BWG"]
theorem multiplicity_kaehlerDifferent_eq_length_stalk (hx : IsClosed ({x} : Set X)) :
    letI := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (kaehlerDifferent f) x) =
      Module.length (ToType (X.sheaf.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf x)) := by
  let := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := (f.stalkMap x).hom.toAlgebra
  have := essFiniteType_stalkMap f x
  obtain ⟨hB, -, -, -⟩ := localRings_of_isClosed pX pY f hf hx
  rw [stalk_kaehlerDifferent_eq_fittingIdeal, length_quotient_fittingIdeal_zero_eq_length]
  exact (Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv
    f x).length_eq.symm

/-- **Stacks Project, Tag 0C1F, part (2).** Let `f : X → Y` be a dominant morphism of smooth
curves over a field and `x ∈ X` a closed point with image `y`. The multiplicity `d_x` of `x` in
the closed subscheme cut out by the different of `f` is at least `e_x - 1`, where `e_x` is the
ramification index of `𝒪_{X,x}` over `𝒪_{Y,y}`. -/
@[stacks 0C1F "(2): `d_x ≥ e_x - 1`, for a dominant morphism of smooth curves; the different is the
Kähler different, which is the different of Tag 0BW4 by Tag 0BWG"]
theorem ramificationIdx_sub_one_le_multiplicity_kaehlerDifferent (hx : IsClosed ({x} : Set X)) :
    letI := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI := (f.stalkMap x).hom.toAlgebra
    ((ramificationIdx (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) - 1 : ℕ) : ℕ∞) ≤
      Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (kaehlerDifferent f) x) := by
  let := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_algebraMap_stalkMap f x
  have := essFiniteType_stalkMap f x
  obtain ⟨_, _, _, _⟩ := localRings_of_isClosed pX pY f hf hx
  rw [stalk_kaehlerDifferent_eq_fittingIdeal]
  exact ramificationIdx_sub_one_le_length_quotient_fittingIdeal

/-- **Stacks Project, Tag 0C1F, part (3).** Let `f : X → Y` be a dominant morphism of smooth
curves over a field and `x ∈ X` a closed point with image `y`. The multiplicity `d_x` of `x` in
the closed subscheme cut out by the different of `f` equals `e_x - 1` if and only if `𝒪_{X,x}` is
tamely ramified over `𝒪_{Y,y}`: the residue field extension `κ(x) / κ(y)` is separable and the
characteristic of `κ(y)` does not divide `e_x`. -/
@[stacks 0C1F "(3): `d_x = e_x - 1` if and only if `𝒪_{X,x}` is tamely ramified over `𝒪_{Y,y}`,
for a dominant morphism of smooth curves; the different is the Kähler different, which is the
different of Tag 0BW4 by Tag 0BWG"]
theorem multiplicity_kaehlerDifferent_eq_iff (hx : IsClosed ({x} : Set X)) :
    letI := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI := (f.stalkMap x).hom.toAlgebra
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (kaehlerDifferent f) x) =
        ((ramificationIdx (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) - 1 : ℕ) : ℕ∞) ↔
      (letI := (f.residueFieldMap x).hom.toAlgebra;
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)) ∧
        ¬ ringChar (Y.residueField (f x)) ∣
          ramificationIdx (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_algebraMap_stalkMap f x
  have := essFiniteType_stalkMap f x
  obtain ⟨_, _, _, _⟩ := localRings_of_isClosed pX pY f hf hx
  rw [stalk_kaehlerDifferent_eq_fittingIdeal, length_quotient_fittingIdeal_eq_iff,
    residueFieldMap_toAlgebra_eq]
  rfl

end Curves

end AlgebraicGeometry

end
