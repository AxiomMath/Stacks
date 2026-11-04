module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistInjectivity
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AmpleFamilyCartier.AmpleFamily
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveDivisorTwist

/-!
# Sections of the twists of an invertible module by an exceptional curve

Let `E ⊆ X` be an exceptional curve of the first kind and `ℒ` an invertible `𝒪_X`-module. For
`m ≥ 0` write `ℒ(mE) = ℒ ⊗ 𝒪_X(E)^{⊗ m}` (`Stacks.Surfaces.divisorTwist`). This file supplies the
two constructions on sections of `ℒ(mE)` that the proof of [Stacks, Tag 0C2M] makes.

* Multiplication by the canonical section `1_E` of `𝒪_X(E)`, iterated `m` times, is a morphism
  `ℒ ⟶ ℒ(mE)`; it sends a global section `t` of `ℒ` to a global section of `ℒ(mE)` whose
  nonvanishing locus is `X_t ∖ E` as soon as `m ≥ 1`.
* If `ℒ` has degree `m ≥ 1` on `E` and `H¹(X, ℒ((m-1)E)) = 0`, then `ℒ(mE)` has a global section
  that does not vanish at any point of `E`: the restriction of `ℒ(mE)` to `E ≅ 𝐏¹` is trivial, so
  it has a nowhere vanishing section, and the vanishing of
  `H¹(X, ℐ_E ⊗ ℒ(mE)) = H¹(X, ℒ((m-1)E))` lifts it to `X`.

## Main definitions

* `Stacks.Surfaces.mulCanonicalSection`: multiplication by `1_E`, `ℱ ⟶ ℱ ⊗ 𝒪_X(E)`.
* `Stacks.Surfaces.divisorTwistMap`: its `m`-th iterate, `ℒ ⟶ ℒ(mE)`.

## Main results

* `Stacks.Surfaces.nonvanishingLocus_divisorTwistMap`: for `m ≥ 1`, the image of a global
  section `t` vanishes exactly on `E ∪ (X ∖ X_t)`.
* `Stacks.Surfaces.exists_section_forall_mem_nonvanishingLocus_divisorTwist`: a global section of
  `ℒ(mE)` generating it at every point of `E`.

## References

* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Tag 0C2J](https://stacks.math.columbia.edu/tag/0C2J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open RingedSpaceModuleAdjunction (modulePullback)
open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)

universe u

namespace Stacks.Surfaces

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric

variable {X : Scheme.{u}}

/-! ### Multiplication by the canonical section -/

/-- The canonical section `1_E` of `𝒪_X(E)`, as a global section. -/
abbrev canonicalGlobalSection (D : X.IdealSheafData) :
    Γ((Stacks.Divisors.invertibleSheaf' D : X.Modules), ⊤) :=
  Stacks.Divisors.canonicalSection D

/-- **Multiplication by the canonical section `1_E`**, the morphism `ℱ ⟶ ℱ ⊗ 𝒪_X(E)` induced by
`𝒪_X ⊆ 𝒪_X(E)`. -/
def mulCanonicalSection (D : X.IdealSheafData) (F : X.Modules) :
    F ⟶ Scheme.Modules.tensorObj F (Stacks.Divisors.invertibleSheaf' D) :=
  (Scheme.Modules.tensorRightUnitor F).inv ≫
    Scheme.Modules.tensorLeftMap F
      (Stacks.EnriquesSeveriZariski.sectionHom _ (canonicalGlobalSection D))

/-- The invertible sheaf `𝒪_X(D)` of an effective Cartier divisor `D` is an invertible module. -/
instance isInvertibleModule_invertibleSheaf' (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.invertibleSheaf' D) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (Stacks.Divisors.stacksIsInvertible_invertibleSheaf D)

/-- `1_E` does not vanish at a point exactly when the point is off `E`. -/
theorem mem_nonvanishingLocus_canonicalGlobalSection_iff (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Divisors.invertibleSheaf' D)
        (canonicalGlobalSection D) ↔ x ∉ D.support :=
  eq_iff_iff.mp (congrArg (fun U : X.Opens => x ∈ U)
    (Stacks.AmpleFamilyCartier.nonvanishingOpen_canonicalSection D))

/-- Off `E`, multiplication by `1_E` is bijective on stalks. -/
theorem bijective_stalkLinearMap_mulCanonicalSection (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : X.Modules) {x : X} (hx : x ∉ D.support) :
    Function.Bijective (stalkLinearMap _ _ (mulCanonicalSection D F) x) :=
  Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_comp _ _ x
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse _ _
      (Scheme.Modules.tensorRightUnitor F).inv_hom_id
      (Scheme.Modules.tensorRightUnitor F).hom_inv_id x)
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_tensorLeftMap F _ x
      (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_sectionHom _ _
        ((mem_nonvanishingLocus_canonicalGlobalSection_iff D x).mpr hx)))

/-- On `E`, multiplication by `1_E` lands in `𝔪_x` times the stalk. -/
theorem mem_maximalSmul_stalkLinearMap_mulCanonicalSection (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : X.Modules) {x : X} (hx : x ∈ D.support)
    (z : F.presheaf.stalk x) :
    stalkLinearMap _ _ (mulCanonicalSection D F) x z ∈
      Stacks.ModuleStalk.maximalSmul
        (Scheme.Modules.tensorObj F (Stacks.Divisors.invertibleSheaf' D)) x :=
  Stacks.EnriquesSeveriZariski.mem_maximalSmul_stalkLinearMap_comp_right _ _ x
    (fun w => Stacks.EnriquesSeveriZariski.mem_maximalSmul_stalkLinearMap_tensorLeftMap F _ x
      (fun w' => Stacks.EnriquesSeveriZariski.mem_maximalSmul_stalkLinearMap_sectionHom _ _
        (fun h => (mem_nonvanishingLocus_canonicalGlobalSection_iff D x).mp h hx) w') w) z

/-- A linear bijection of modules over a local ring preserves `𝔪 · ⊤` in both directions. -/
theorem mem_ideal_smul_top_iff_of_bijective {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (g : M →ₗ[R] N)
    (hg : Function.Bijective g) (z : M) :
    g z ∈ I • (⊤ : Submodule R N) ↔ z ∈ I • (⊤ : Submodule R M) := by
  let e := LinearEquiv.ofBijective g hg
  exact ⟨fun h => by simpa [e] using
    Stacks.SheafOfModules.map_mem_ideal_smul_top I e.symm.toLinearMap h,
    Stacks.SheafOfModules.map_mem_ideal_smul_top I g⟩

/-- A morphism of modules whose stalk map at `x` is bijective preserves vanishing at `x` of a
global section, in both directions. -/
theorem mem_nonvanishingLocus_app_iff_of_bijective {F G : X.Modules} (φ : F ⟶ G) (t : Γ(F, ⊤))
    {x : X} (hφ : Function.Bijective (stalkLinearMap _ _ φ x)) :
    x ∈ Stacks.Ample.nonvanishingLocus G (φ.app ⊤ t) ↔
      x ∈ Stacks.Ample.nonvanishingLocus F t := by
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, Stacks.Ample.mem_nonvanishingLocus_iff,
    ← Stacks.ModuleStalk.mapFun_Γgerm]
  exact not_congr (mem_ideal_smul_top_iff_of_bijective _ (stalkLinearMap _ _ φ x) hφ _)

/-- **The nonvanishing locus of `1_E · t`** is `X_t ∖ E`. -/
theorem nonvanishingLocus_mulCanonicalSection (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : X.Modules) (t : Γ(F, ⊤)) :
    Stacks.Ample.nonvanishingLocus _ ((mulCanonicalSection D F).app ⊤ t) =
      Stacks.Ample.nonvanishingLocus F t ∩ (D.support : Set X)ᶜ := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_compl_iff]
  by_cases hx : x ∈ D.support
  · refine iff_of_false (fun h => ?_) (fun h => h.2 hx)
    refine (Stacks.Ample.mem_nonvanishingLocus_iff _ _ x).mp h ?_
    convert mem_maximalSmul_stalkLinearMap_mulCanonicalSection D F hx
      ((F.presheaf.Γgerm x).hom t) using 1
    exact (Stacks.ModuleStalk.mapFun_Γgerm (mulCanonicalSection D F) x t).symm
  · exact (mem_nonvanishingLocus_app_iff_of_bijective _ t
      (bijective_stalkLinearMap_mulCanonicalSection D F hx)).trans
      ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

/-! ### The iterated multiplication `ℒ ⟶ ℒ(mE)` -/

/-- **The morphism `ℒ ⟶ ℒ(mE)`**, multiplication by `1_E^{⊗ m}`, defined by recursion on `m`. -/
def divisorTwistMap (D : X.IdealSheafData) (A : X.Modules) : (m : ℕ) → (A ⟶ divisorTwist D A m)
  | 0 => 𝟙 A
  | m + 1 => divisorTwistMap D A m ≫ mulCanonicalSection D (divisorTwist D A m)

/-- `ℒ ⟶ ℒ(0E)` is the identity. -/
theorem divisorTwistMap_zero (D : X.IdealSheafData) (A : X.Modules) :
    divisorTwistMap D A 0 = 𝟙 A := rfl

/-- `ℒ ⟶ ℒ((m+1)E)` is `ℒ ⟶ ℒ(mE)` followed by multiplication by `1_E`. -/
theorem divisorTwistMap_succ (D : X.IdealSheafData) (A : X.Modules) (m : ℕ) :
    divisorTwistMap D A (m + 1) =
      divisorTwistMap D A m ≫ mulCanonicalSection D (divisorTwist D A m) := rfl

/-- **For `m ≥ 1`, the image of a global section `t` of `ℒ` in `ℒ(mE)` has nonvanishing locus
`X_t ∖ E`.** -/
theorem nonvanishingLocus_divisorTwistMap (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (A : X.Modules) (t : Γ(A, ⊤)) :
    ∀ m : ℕ, 1 ≤ m →
      Stacks.Ample.nonvanishingLocus (divisorTwist D A m) ((divisorTwistMap D A m).app ⊤ t) =
        Stacks.Ample.nonvanishingLocus A t ∩ (D.support : Set X)ᶜ
  | 0, h => by omega
  | 1, _ => by
    show Stacks.Ample.nonvanishingLocus _
      ((mulCanonicalSection D A).app ⊤ ((𝟙 A : A ⟶ A).app ⊤ t)) = _
    rw [Scheme.Modules.Hom.id_app]
    exact nonvanishingLocus_mulCanonicalSection D A t
  | m + 2, _ => by
    show Stacks.Ample.nonvanishingLocus _
      ((mulCanonicalSection D (divisorTwist D A (m + 1))).app ⊤
        ((divisorTwistMap D A (m + 1)).app ⊤ t)) = _
    exact (nonvanishingLocus_mulCanonicalSection D _ _).trans
      (by rw [nonvanishingLocus_divisorTwistMap D A t (m + 1) (by omega), Set.inter_assoc,
        Set.inter_self])

/-! ### A section of `ℒ(mE)` generating it along `E` -/

/-- The unit section of `𝒪_X` vanishes nowhere. -/
theorem mem_nonvanishingLocus_one (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule X)
      (show Γ(Stacks.Ample.unitModule X, ⊤) from (1 : Γ(X, ⊤))) :=
  (Stacks.Ample.mem_nonvanishingLocus_iff _ _ x).mpr
    (Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one X x _ rfl)

/-- **A nowhere vanishing global section of `ℒ(mE)` along `E`.** Let `E` be an exceptional curve
of the first kind and `ℒ` an invertible module of degree `m ≥ 1` on `E`. If
`H¹(X, ℒ((m-1)E)) = 0`, then `ℒ(mE)` has a global section that does not vanish at any point of
`E`.

The restriction of `ℒ(mE)` to `E ≅ 𝐏¹` is `𝒪(m - m) = 𝒪`, so it has a nowhere vanishing section
over `E`; the obstruction to lifting it to `X` is `H¹(X, ℐ_E ⊗ ℒ(mE))`, and
`ℐ_E ⊗ ℒ(mE) ≅ ℒ((m-1)E)`. -/
theorem exists_section_forall_mem_nonvanishingLocus_divisorTwist (D : X.IdealSheafData)
    (k : Type u) [Field k] {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (m : ℕ)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m + 1))
    (hH1 : IsZero (((moduleGlobalSections X).rightDerived 1).obj (divisorTwist D A m))) :
    ∃ s : Γ(divisorTwist D A (m + 1), ⊤), ∀ z : D.subscheme,
      D.subschemeι.base z ∈ Stacks.Ample.nonvanishingLocus (divisorTwist D A (m + 1)) s := by
  have _hcart := hE.isEffectiveCartierDivisor
  set M := divisorTwist D A (m + 1)
  have hMinv : Stacks.Ample.IsInvertibleModule X M := isInvertible_divisorTwist D A (m + 1)
  -- the obstruction group
  have hvan : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj
          (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)).obj M)) := by
    have e1 : MonoidalCategory.tensorObj
        (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (Stacks.Divisors.negativeTwist' D) M ≅ divisorTwist D A m :=
      BraidedCategory.braiding
        (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) _ M ≪≫
        twistedIdealIso D (divisorTwist D A m)
    exact IsZero.of_iso hH1 (((moduleGlobalSections X).rightDerived 1).mapIso e1)
  -- the restriction of `M` to `𝐏¹` is trivial
  obtain ⟨hdeg'⟩ := nonempty_pullbackDivisorTwistIso D k hE A hdeg (m + 1)
  let N := (modulePullback D.subschemeι.toLRSHom.toShHom).obj M
  have hNinv : Stacks.Ample.IsInvertibleModule D.subscheme N :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback D.subschemeι M
  have hN1 : Stacks.Ample.IsInvertibleModule (projectiveLineProj k)
      ((modulePullback e.hom.toLRSHom.toShHom).obj N) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback e.hom N
  let triv : ((modulePullback e.hom.toLRSHom.toShHom).obj N : (projectiveLineProj k).Modules) ≅
      Stacks.Ample.unitModule (projectiveLineProj k) :=
    hdeg' ≪≫ eqToIso (congrArg _ (by push_cast; ring)) ≪≫
      Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)
  let τ : Γ((modulePullback e.hom.toLRSHom.toShHom).obj N, ⊤) :=
    Scheme.Modules.Hom.app triv.inv ⊤
      (show Γ(Stacks.Ample.unitModule (projectiveLineProj k), ⊤) from
        (1 : Γ(projectiveLineProj k, ⊤)))
  have hτ : ∀ p, p ∈ Stacks.Ample.nonvanishingLocus _ τ := fun p => by
    rw [show τ = Scheme.Modules.Hom.app triv.symm.hom ⊤ _ from rfl,
      Stacks.Ample.nonvanishingLocus_congr triv.symm]
    exact mem_nonvanishingLocus_one p
  -- descend `τ` along the isomorphism `e`
  obtain ⟨g, hg⟩ := (Scheme.Modules.bijective_pullbackGlobalSection_of_isIso_c e.hom N).2 τ
  have hgz : ∀ z : D.subscheme, z ∈ Stacks.Ample.nonvanishingLocus N g := fun z => by
    obtain ⟨p, rfl⟩ : ∃ p, e.hom.base p = z :=
      ⟨e.inv.base z, by
        show (e.inv ≫ e.hom).base z = z
        rw [e.inv_hom_id]
        rfl⟩
    refine (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff e.hom N g p).mp ?_
    rw [hg]
    exact hτ p
  -- lift `g` to `X`
  obtain ⟨s, hs⟩ := Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1
    D.subschemeι M hvan g
  refine ⟨s, fun z => ?_⟩
  refine (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff D.subschemeι M s z).mp ?_
  rw [hs]
  exact hgz z

end Stacks.Surfaces

end
