module

public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-zero direct image of the structure sheaf of projective space

Let `S` be a scheme, let `n` be a natural number and let `f : ℙⁿ_S ⟶ S` be the structure
morphism of projective `n`-space over `S`. The direct image of the structure sheaf of `ℙⁿ_S` is
the structure sheaf of `S`:

`f_* 𝒪_{ℙⁿ_S} = 𝒪_S`.

This is stated here as the invertibility of the canonical map on sections, over every affine
open `V` of the base: `f` induces an isomorphism `Γ(S, V) ≅ Γ(ℙⁿ_S, f⁻¹V)`, and the sections of
`f_* 𝒪_{ℙⁿ_S}` over `V` are by definition the sections of `𝒪_{ℙⁿ_S}` over `f⁻¹V`.

The names in the list below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main results

* `isIso_appTop_structureMorphism_projectiveSpaceOverRing`: **`Γ(ℙⁿ_{Spec R}, 𝒪) = R`** on the
  library's model of projective space, for every commutative ring `R`.
* `isIso_appTop_structureMorphism_projectiveSpaceOver`: the same over an arbitrary affine base
  scheme.
* `isIso_app_structureMorphism_projectiveSpaceOver` and
  `bijective_app_structureMorphism_projectiveSpaceOver`: **`f_* 𝒪_{ℙⁿ_S} = 𝒪_S`**, in the form
  that the structure morphism induces an isomorphism on the sections over every affine open of
  the base.
* `isIso_appTop_of_sq` and `isIso_app_of_isIso_appTop_morphismRestrict`: invertibility of the
  map on sections is invariant under isomorphisms of morphisms and passes from the restriction
  to an open of the target.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Two transport lemmas -/

/-- An isomorphism of schemes induces an invertible map on global sections. -/
private theorem isIso_appTop_hom {X Y : Scheme.{u}} (e : X ≅ Y) : IsIso e.hom.appTop :=
  inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))

/-- **Transport of the map on global sections along an isomorphism of morphisms.** If
`f ≫ β = α ≫ f'` with `α` and `β` isomorphisms of schemes, then `f` induces an invertible map on
global sections as soon as `f'` does. -/
theorem isIso_appTop_of_sq {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (α : X ≅ X') (β : Y ≅ Y') (hsq : f ≫ β.hom = α.hom ≫ f') (hf' : IsIso f'.appTop) :
    IsIso f.appTop := by
  have := isIso_appTop_hom α
  have := isIso_appTop_hom β
  have key : β.hom.appTop ≫ f.appTop = f'.appTop ≫ α.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hsq]
  have h : f.appTop = inv β.hom.appTop ≫ f'.appTop ≫ α.hom.appTop := by
    rw [← key, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- **Sections over an open of the target are global sections of the restriction.** If the
restriction of `f` to an open `U` of the target induces an invertible map on global sections,
then `f` induces an invertible map on the sections over `U`. -/
theorem isIso_app_of_isIso_appTop_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (h : IsIso ((f ∣_ U).appTop)) : IsIso (f.app U) := by
  replace h : IsIso ((f ∣_ U).app ⊤) := h
  rw [morphismRestrict_app'] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr f _ (Scheme.Opens.ι_image_top U)
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)) (fun g => IsIso g)).mp h

/-! ### The identification over an affine base -/

/-- The ring homomorphism from `R` to the degree-zero part of `R[T₀, …, Tₙ]` for the
total-degree grading, taken as the degree-zero component of `algebraMap`, is
`Stacks.ProjectiveCohomology.polyDegreeZeroHom`. -/
theorem polyDegreeZeroHom_eq (R : Type u) [CommRing R] (n : ℕ) :
    CommRingCat.ofHom ((GradedRing.projZeroRingHom'
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).comp
      (algebraMap R (MvPolynomial (Fin (n + 1)) R)))
      = Stacks.ProjectiveCohomology.polyDegreeZeroHom R n := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  change ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.C r)) 0 : MvPolynomial (Fin (n + 1)) R) = MvPolynomial.C r
  exact DirectSum.decompose_of_mem_same _
    ((MvPolynomial.mem_homogeneousSubmodule 0 _).2 (MvPolynomial.isHomogeneous_C _ r))

/-- **`Γ(ℙⁿ_{Spec R}, 𝒪) = R`**, on the library's model of projective space: the structure
morphism `ℙⁿ_{Spec R} ⟶ Spec R` induces an isomorphism on global sections, for every
commutative ring `R` and every `n`. -/
@[sga "7 XI 1.1" "1.1(ii), special case"]
theorem isIso_appTop_structureMorphism_projectiveSpaceOverRing (n : ℕ) (R : CommRingCat.{u}) :
    IsIso ((projectiveSpaceOverRing n R ↘ Spec R).appTop) := by
  have hname : Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n
      = Stacks.ProjectiveCohomology.projModelToSpec R n :=
    congrArg (fun φ => AlgebraicGeometry.Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫ Spec.map φ)
      (polyDegreeZeroHom_eq R n)
  have hcomp : IsIso ((Scheme.ΓSpecIso R).inv ≫
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections R n
  have hproj : IsIso ((Stacks.ProjectiveCohomology.projModelToSpec R n).appTop) := by
    rw [← hname]
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso R).inv _
  rw [← Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism R n,
    Scheme.Hom.comp_appTop] at hproj
  replace hproj : IsIso ((projectiveSpaceOverRing n R ↘ Spec R).appTop ≫
    (Stacks.ProjectiveCohomology.projModelIso (R : Type u) n).hom.appTop) := hproj
  have := isIso_appTop_hom (Stacks.ProjectiveCohomology.projModelIso (R : Type u) n)
  exact IsIso.of_isIso_comp_right _
    (Stacks.ProjectiveCohomology.projModelIso (R : Type u) n).hom.appTop

/-- **`Γ(ℙⁿ_S, 𝒪) = Γ(S, 𝒪)` over an affine base scheme `S`.** The structure morphism of `ℙⁿ_S`
induces an isomorphism on global sections. -/
theorem isIso_appTop_structureMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u})
    [IsAffine S] : IsIso ((projectiveSpaceOver n S ↘ S).appTop) := by
  have : IsIso (projectiveSpaceOverMap n S.isoSpec.hom) :=
    (isPullback_projectiveSpaceOverMap n S.isoSpec.hom).isIso_fst_of_isIso
  refine isIso_appTop_of_sq _ (projectiveSpaceOver n (Spec Γ(S, ⊤)) ↘ Spec Γ(S, ⊤))
    (asIso (projectiveSpaceOverMap n S.isoSpec.hom)) S.isoSpec ?_
    (isIso_appTop_structureMorphism_projectiveSpaceOverRing n Γ(S, ⊤))
  rw [asIso_hom]
  exact (projectiveSpaceOverMap_fst n S.isoSpec.hom).symm

/-! ### The degree-zero identification over an arbitrary base -/

/-- **The degree-zero identification `f_* 𝒪_{ℙⁿ_S} = 𝒪_S`.** For the structure morphism
`f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S` and an arbitrary `n`, the canonical map
`𝒪_S ⟶ f_* 𝒪_{ℙⁿ_S}` is an isomorphism on the sections over every affine open `V` of the base:
`f` induces an isomorphism `Γ(S, V) ≅ Γ(ℙⁿ_S, f⁻¹V)`.

Since the affine opens form a basis of `S` and a morphism of sheaves that is invertible on a
basis is invertible, this is the full assertion that the direct image of the structure sheaf of
`ℙⁿ_S` is the structure sheaf of `S`. -/
@[stacks 01XW "the degree-zero clause at the zeroth twist, sectionwise and for the underived \
direct image: the structure morphism of ℙⁿ_S induces an isomorphism Γ(S, V) ≅ Γ(ℙⁿ_S, f⁻¹V) for \
every affine open V of the base, which is f_* 𝒪 = 𝒪_S on a basis of opens. The degree-zero row \
at every twist, assembled as an isomorphism of module sheaves on S and in the R⁰ f_* spelling, \
is ProjectiveSpaceHigherDirectImage.baseDegreeSheafIsoPushforwardTwistOver and \
...baseDegreeSheafIsoRightDerivedPushforwardTwistOver in ...DegreeZeroRow; the whole display, \
its three rows in one statement at n >= 1, is \
...rightDerivedPlusPushforwardTwistOverDisplay in ...Display"]
theorem isIso_app_structureMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) {V : S.Opens}
    (hV : IsAffineOpen V) : IsIso ((projectiveSpaceOver n S ↘ S).app V) := by
  have hA := isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) V
  have hB := (isPullback_projectiveSpaceOverMap n V.ι).flip
  have : IsAffine V.toScheme := hV
  refine isIso_app_of_isIso_appTop_morphismRestrict _ _ ?_
  refine isIso_appTop_of_sq _ (projectiveSpaceOver n V.toScheme ↘ V.toScheme)
    (hA.isoIsPullback _ _ hB) (Iso.refl _) ?_
    (isIso_appTop_structureMorphism_projectiveSpaceOver n V.toScheme)
  rw [Iso.refl_hom, Category.comp_id]
  exact (IsPullback.isoIsPullback_hom_fst _ _ hA hB).symm

/-- **The degree-zero identification, read as a bijection.** The structure morphism of `ℙⁿ_S`
carries the sections of `𝒪_S` over an affine open `V` bijectively onto the sections of
`𝒪_{ℙⁿ_S}` over `f⁻¹V`. -/
theorem bijective_app_structureMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u})
    {V : S.Opens} (hV : IsAffineOpen V) :
    Function.Bijective ((projectiveSpaceOver n S ↘ S).app V) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_app_structureMorphism_projectiveSpaceOver n S hV)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
