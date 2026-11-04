module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveDualityPlusBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveHigherDirectImageLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleDerivedHomInverseImagePerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# `Rf_* Λ` is perfect for a smooth proper curve

Let `S` be a Noetherian scheme on which the prime `ℓ` is invertible, `Λ = ℤ/ℓ`, and `f : X ⟶ S`
proper and smooth with fibres of dimension at most one. All names below are in the namespace
`Stacks.EtaleCohomology`. The complex `K = Rf_*(f⁻¹ Λ_S)` (`curveDualityComplex`, unbounded
derived direct image) has cohomology in degrees `[0, 2]` only, and its cohomology sheaves
`Rᵠ f_* Λ` are locally constant of finite type. Hence `K` is a perfect object of the derived
category of modules over the constant ringed site `(S_étale, Λ̲)`
(`isPerfect_curveDualityComplex`), and the comparison `g⁻¹ RHom(K, M) ⟶ RHom(g⁻¹K, g⁻¹M)` of
Stacks 08JF is an isomorphism for every `g` and every `M`
(`isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex`).

The vanishing `Rᵠ f_* Λ = 0` for `q > 2` is [Stacks, Tag 095U] for sheaves of modules
(`isZero_rightDerived_etaleModuleDirectImage_of_isProper`); the local constancy is case (a) of the
proof of [Stacks, Tag 0GKV]
(`isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf`), both on `D⁺`,
carried to the unbounded direct image by `etaleModuleDerivedDirectImagePlusIso`.

This is the perfectness of `Rf_* Λ` used in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, as a local instance.

## Main results

* `isGE_curveDualityComplex`, `isLE_curveDualityComplex`.
* `isFiniteTypeLocallyConstant_homology_curveDualityComplex`.
* `isPerfect_curveDualityComplex`.
* `isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex`, and its form
  `..._of_smoothOfRelativeDimension` over a base smooth over a field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor

variable (ℓ : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`K = Rf_*(f⁻¹Λ_S)` is the derived direct image on `D⁺`**: the unbounded derived direct image
of `E = f⁻¹(Λ_S[0])` is the image in `D` of the bounded below one of `f⁻¹Λ_S` placed in degree
zero. -/
def curveDualityComplexPlusIso :
    DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f).obj
      (curveDualityUnitPlus ℓ f)) ≅ curveDualityComplex ℓ f :=
  (etaleModuleDerivedDirectImagePlusIso.{u} (ZMod ℓ) f).app (curveDualityUnitPlus ℓ f) ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).mapIso (curveDualityUnitPlusIso ℓ f)

/-- The cohomology sheaves of `K = Rf_*(f⁻¹Λ_S)` are those of the bounded below direct image. -/
def homologyCurveDualityComplexIso (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ p).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f).obj (curveDualityUnitPlus ℓ f)) ≅
      (DerivedCategory.homologyFunctor _ p).obj (curveDualityComplex ℓ f) :=
  (DerivedCategory.homologyFunctor _ p).mapIso (curveDualityComplexPlusIso ℓ f)

/-- **`Hᵖ(Rf_*(f⁻¹Λ_S)) = 0` for `p < 0`**: a derived direct image of a sheaf has no cohomology
in negative degrees. -/
theorem isZero_homology_curveDualityComplex_of_neg (p : ℤ) (hp : p < 0) :
    IsZero ((DerivedCategory.homologyFunctor _ p).obj (curveDualityComplex ℓ f)) :=
  ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) f).isZero_rightDerivedPlus_of_neg _ p hp).of_iso
    (homologyCurveDualityComplexIso ℓ f p).symm

/-- **`Hᵖ(Rf_*(f⁻¹Λ_S)) = Rᵖ f_* Λ = 0` for `p > 2`** when `f` is proper with fibres of
dimension at most one ([Stacks, Tag 095U], `ℤ/ℓ` being torsion). -/
theorem isZero_homology_curveDualityComplex_of_two_lt [NeZero ℓ] [IsProper f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) (p : ℤ) (hp : 2 < p) :
    IsZero ((DerivedCategory.homologyFunctor _ p).obj (curveDualityComplex ℓ f)) := by
  refine IsZero.of_iso ?_ (homologyCurveDualityComplexIso ℓ f p).symm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ p by omega)
  refine IsZero.of_iso ?_
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} (ZMod ℓ) f) n).app
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))).symm
  exact isZero_rightDerived_etaleModuleDirectImage_of_isProper (ZMod ℓ) f 1 hdim _
    (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero (ZMod ℓ) ℓ
      (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (ZMod.natCast_self ℓ) _) n (by omega)

/-- **`K = Rf_*(f⁻¹Λ_S)` lies in degrees `≥ 0`.** -/
theorem isGE_curveDualityComplex : (curveDualityComplex ℓ f).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  exact fun p hp => isZero_homology_curveDualityComplex_of_neg ℓ f p hp

/-- **`K = Rf_*(f⁻¹Λ_S)` lies in degrees `≤ 2`** for `f` proper with fibres of dimension at most
one ([Stacks, Tag 095U]). -/
theorem isLE_curveDualityComplex [NeZero ℓ] [IsProper f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) : (curveDualityComplex ℓ f).IsLE 2 := by
  rw [DerivedCategory.isLE_iff]
  exact fun p hp => isZero_homology_curveDualityComplex_of_two_lt ℓ f hdim p hp

/-- **The cohomology sheaves `Rᵖ f_* Λ` of `K = Rf_*(f⁻¹Λ_S)` are locally constant of finite
type**, for `f` proper and smooth with fibres of dimension at most one over a Noetherian base on
which `ℓ` is invertible (case (a) of the proof of [Stacks, Tag 0GKV]). -/
theorem isFiniteTypeLocallyConstant_homology_curveDualityComplex [Fact ℓ.Prime] [IsProper f]
    [Smooth f] (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) [IsNoetherian S]
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (p : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      S.smallEtaleTopology (ZMod ℓ)
      ((DerivedCategory.homologyFunctor _ p).obj (curveDualityComplex ℓ f)) :=
  ObjectProperty.prop_of_iso _ (homologyCurveDualityComplexIso ℓ f p)
    (isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf f hdim ℓ hℓ p)

section Perfect

-- The locally small model `SheafOfModules.hasDerivedCategory` of `D(S_étale, Λ̲)` would be found
-- before the standard one, in which
-- `Stacks.EtaleCohomology.isPerfect_etaleDerivedEquivalence_functor_obj` is stated.

/-- **`Rf_* Λ` is perfect** (Stacks 08G5) on the constant ringed site `(S_étale, Λ̲)`, `Λ = ℤ/ℓ`,
for `f : X ⟶ S` proper and smooth with fibres of dimension at most one over a Noetherian base on
which `ℓ` is invertible: it has cohomology in degrees `[0, 2]` only, all of it locally constant of
finite type, over the field `ℤ/ℓ`. -/
theorem isPerfect_curveDualityComplex [Fact ℓ.Prime] [IsProper f] [Smooth f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) [IsNoetherian S]
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) :
    AlgebraicGeometry.RingedSite.IsPerfect
      (etaleRingedSite.{u, 0} (ZMod ℓ) S)
      ((etaleDerivedEquivalence.{u, 0} (ZMod ℓ) S).functor.obj (curveDualityComplex ℓ f)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hGE := isGE_curveDualityComplex ℓ f
  have hLE := isLE_curveDualityComplex ℓ f hdim
  exact isPerfect_etaleDerivedEquivalence_functor_obj (curveDualityComplex ℓ f) 0 2
    (isFiniteTypeLocallyConstant_homology_curveDualityComplex ℓ f hdim hℓ)

/-- **Stacks 08JF at `K = Rf_* Λ`**: for `f : X ⟶ S` proper and smooth with fibres of dimension at
most one over a Noetherian base on which `ℓ` is invertible, every morphism `g : Y ⟶ S` (for
instance a geometric point) and every `M`, the comparison
`g⁻¹ RHom(Rf_* Λ, M) ⟶ RHom(g⁻¹ Rf_* Λ, g⁻¹ M)` is an isomorphism, `Rf_* Λ` being perfect. -/
theorem isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex [Fact ℓ.Prime]
    [IsProper f] [Smooth f] (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    [IsNoetherian S] (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) {Y : Scheme.{u}} (g : Y ⟶ S)
    (M : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S)) :
    IsIso (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) g (curveDualityComplex ℓ f) M) :=
  isIso_etaleDerivedInverseImageHomComparison_of_isPerfect (ZMod ℓ) g _ M
    (isPerfect_curveDualityComplex ℓ f hdim hℓ)

end Perfect

/-- **Stacks 08JF at `K = Rf_* Λ`, over a base smooth over a field**: for `S` affine and smooth
over a field `k` in which `ℓ` is invertible and `f : X ⟶ S` a smooth projective morphism of
relative dimension one (the setting of `Stacks.EtaleCohomology.CurveDualityStalkComparison`), every
`g : Y ⟶ S` and every `M`, `g⁻¹ RHom(Rf_* Λ, M) ⟶ RHom(g⁻¹ Rf_* Λ, g⁻¹ M)` is an isomorphism. -/
theorem isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex_of_smoothOfRelativeDimension
    [Fact ℓ.Prime] (k : Type u) [Field k] (hℓ : IsUnit (ℓ : k)) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] [SmoothOfRelativeDimension 1 f]
    (hf : IsProjectiveMorphism f) {Y : Scheme.{u}} (g : Y ⟶ S)
    (M : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S)) :
    IsIso
      (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) g (curveDualityComplex ℓ f) M) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  have : IsProper f := isProper_of_isProjectiveMorphism f hf
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex ℓ f
    (fun s => topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 f s)
    (isUnit_natCast_sections k q hℓ) g M

end Stacks.EtaleCohomology

end
