module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackAffineChart
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveBundleFormsVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.PushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 0FUR: forms on the projective bundle of the coordinate blowup

Fix a ring `R`, put `S = Spec R`, let `Z = 𝐀^m_S` be the centre of the standard coordinate blowup
of `𝐀^{m+n}_S` and `p : P = 𝐏^{n-1}_Z ⟶ Z` its projective bundle. Clause (2) of
[Stacks, Tag 0FUR] says that the canonical map

`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}`

(`Stacks.DeRham.coordinateBundleFormsDirectImage`) is an isomorphism for every `a ≥ 0`. This file
proves it for every `n` and every `a`.

## The proof

It is the source's. `P = Z ×_S 𝐏^{n-1}_S`, and the product decomposition (Tag 0FMA, in the form
`Stacks.DeRham.coordinateBundleFormsProductIso`) writes `Ω^a_{P/S}` as the direct sum over
`a = r + s` of `pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}`. Push forward along `p = pr₁`. By the
projection formula (Tag 01E8; `Ω^r_{Z/S}` is finite free) the `(r, s)` summand becomes
`Ω^r_{Z/S} ⊗ pr_{1,*}pr_2^*Ω^s_{𝐏^{n-1}_S/S}`. For `s > 0` that factor vanishes: by base change it
is `pr_{1,*}Ω^s_{𝐏^{n-1}_Z/Z}`, a quasi-coherent module on the affine `Z` whose global sections
`H⁰(𝐏^{n-1}_Z, Ω^s)` are zero by Tag 0FUK. For `s = 0` it is `pr_{1,*}𝒪 = 𝒪_Z`. Hence
`p_*Ω^a_{P/S} ≅ Ω^a_{Z/S}` (`Stacks.DeRham.coordinateBundleFormsPushforwardIso`).

The source then reads off that the canonical map is this identification. Here that step is
replaced by an argument that does not need the compatibility of the product decomposition with the
canonical map. `p` has a section, so the canonical map is a split monomorphism; its target is
isomorphic to its source, which is finite free on the affine `Z`; and a split monomorphism of
quasi-coherent modules on an affine scheme between isomorphic modules with finite global sections
is an isomorphism, a surjective endomorphism of a finite module being injective.

## Main results

* `Stacks.DeRham.coordinateBundleFormsPushforwardIso`: `p_*Ω^a_{P/S} ≅ Ω^a_{Z/S}` for `n ≥ 2`.
* `Stacks.DeRham.isIso_coordinateBundleFormsDirectImage`: **[Stacks, Tag 0FUR], clause (2)**, for
  every `n` and every `a`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m k : ℕ)

/-- **`Γ(Z ×_S 𝐏^{n-1}_S, Ω^s_{/Z}) = 0` for `s ≥ 1` and `n ≥ 2`**: the fibre product is
`𝐏^{n-1}_Z` over `Z = Spec R[x₁, …, x_m]` (`Stacks.DeRham.coordinateBundleProductIso`), which has
no global forms of positive degree relative to its base. -/
theorem subsingleton_sections_coordinateBundleProduct_forms (s : ℕ) (hs : s ≠ 0) :
    Subsingleton Γ(Scheme.Hom.relativeDifferentialForms
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R (k + 2)))
      s, ⊤) :=
  Scheme.Hom.subsingleton_sections_relativeDifferentialForms_of_iso
    (coordinateBundleProductIso R m (k + 2))
    (coordinateBundleProductIso_hom_comp_toCentre R m (k + 2)) s
    (AlgebraicGeometry.ProjectiveSpaceHodge.subsingleton_sections_forms_projectiveSpaceOverRing
      (MvPolynomial (Fin m) R) k s hs)

/-- The canonical map `pr₂^*Ω^s_{𝐏^{n-1}_S/S} ⟶ Ω^s_{Z ×_S 𝐏^{n-1}_S/Z}` of the cartesian
square `Z ×_S 𝐏^{n-1}_S ⟶ 𝐏^{n-1}_S` over `Z ⟶ S`; an isomorphism by [Stacks, Tag 0FL5]. -/
abbrev coordinateBundleFormsBaseChange (s : ℕ) :=
  Scheme.Hom.relativeDifferentialFormsMap
    (pullback.snd (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R k))
    (coordinateBundleAmbientToBase R k)
    (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R k))
    (coordinateBlowupCentreToBase R m)
    (IsPullback.of_hasPullback _ _).flip.w s

/-- [Stacks, Tag 0FL5]: the base change map of forms of a cartesian square is invertible. -/
instance isIso_coordinateBundleFormsBaseChange (s : ℕ) :
    IsIso (coordinateBundleFormsBaseChange R m k s) :=
  Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback _ _).flip s

/-- The direct image of a module of relative differential forms along a qcqs morphism is
quasi-coherent. -/
private instance isQuasicoherent_pushforward_relativeDifferentialForms {X Y S : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : X ⟶ S) (s : ℕ) :
    ((Scheme.Modules.pushforward f).obj
      (Scheme.Hom.relativeDifferentialForms g s)).IsQuasicoherent :=
  AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward f _
    (Scheme.Hom.isQuasicoherent_relativeDifferentialForms g s)

/-- **`pr_{1,*}pr_2^*Ω^s_{𝐏^{n-1}_S/S} = 0` for `s ≥ 1` and `n ≥ 2`**, the vanishing the source
quotes from the proof of [Stacks, Tag 0FMI]: by base change it is `pr_{1,*}Ω^s_{/Z}`, a
quasi-coherent module on the affine `Z` with no global sections. -/
theorem isZero_pushforward_pullback_coordinateBundleAmbientForms (s : ℕ) (hs : s ≠ 0) :
    IsZero ((Scheme.Modules.pushforward
      (pullback.fst (coordinateBlowupCentreToBase R m)
        (coordinateBundleAmbientToBase R (k + 2)))).obj
        ((Scheme.Modules.pullback
          (pullback.snd (coordinateBlowupCentreToBase R m)
            (coordinateBundleAmbientToBase R (k + 2)))).obj
          (Scheme.Hom.relativeDifferentialForms (coordinateBundleAmbientToBase R (k + 2)) s))) := by
  refine IsZero.of_iso ?_ ((Scheme.Modules.pushforward _).mapIso
    (asIso (coordinateBundleFormsBaseChange R m (k + 2) s)))
  exact Stacks.Divisors.Eta.isZero_of_subsingleton_sections_top _
    (subsingleton_sections_coordinateBundleProduct_forms R m k s hs)

/-- The centre `Z = 𝐀^m_S` is smooth over `S`. -/
instance smooth_coordinateBlowupCentreToBase : Smooth (coordinateBlowupCentreToBase R m) :=
  Stacks.MoreMorphisms.smooth_specMap _ (Stacks.MoreMorphisms.smooth_mvPolynomial_C R (Fin m))

/-- The forms `Ω^r_{Z/S}` of the centre are finite locally free. -/
instance isFiniteLocallyFree_coordinateCentreForms (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (coordinateBlowupCentre R m).ringCatSheaf)
      (Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (r : ℤ)) :=
  AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms _ r

/-- **The summands with `s ≥ 1` push forward to zero**: by the projection formula
`p_*(pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}) = Ω^r_{Z/S} ⊗ p_*pr₂^*Ω^s_{𝐏^{n-1}_S/S} = 0`. -/
theorem isZero_pushforward_coordinateBundleFormsSummand (a : ℕ)
    (j : Scheme.Hom.deRhamBoxIndex a) (hj : j.1.2 ≠ 0) :
    IsZero ((Scheme.Modules.pushforward
      (pullback.fst (coordinateBlowupCentreToBase R m)
        (coordinateBundleAmbientToBase R (k + 2)))).obj
        (Scheme.Hom.relativeFormsProductSummand (coordinateBlowupCentreToBase R m)
          (coordinateBundleAmbientToBase R (k + 2)) a j)) :=
  IsZero.of_iso (Stacks.AffineProjectionFormula.isZero_pushforward_tensor_pullback
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R (k + 2)))
      _ _ (isZero_pushforward_pullback_coordinateBundleAmbientForms R m k j.1.2 hj))
    ((Scheme.Modules.pushforward _).mapIso
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap _ _ _))

/-- In degree zero the comparison map of the first projection of `Z ×_S 𝐏^{n-1}_S` is an
isomorphism: it is `𝒪_Z ⟶ pr_{1,*}𝒪`, and the direct image of the structure sheaf of projective
space is the structure sheaf of the base. -/
theorem isIso_formsDirectImageComparison_coordinateBundleProduct_zero (n : ℕ) :
    IsIso (Scheme.Hom.formsDirectImageComparison
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n))
      (coordinateBlowupCentreToBase R m) 0) := by
  refine Scheme.Hom.isIso_formsDirectImageComparison_zero_of_bijective_app _ _ fun V => ?_
  rw [← coordinateBundleProductIso_hom_comp_toCentre R m n]
  open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage in
  have h1 := isIso_app_structureMorphism_projectiveSpaceOver (n - 1)
    (coordinateBlowupCentre R m) V.2
  have h2 : IsIso ((coordinateBundleProductIso R m n).hom.app
      (coordinateBlowupBundleToCentre R m n ⁻¹ᵁ V.1)) := inferInstance
  have h3 : IsIso (((coordinateBundleProductIso R m n).hom ≫
      coordinateBlowupBundleToCentre R m n).app V.1) := by
    rw [Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' h1 h2
  exact (ConcreteCategory.isIso_iff_bijective _).mp h3

/-- **`pr_{1,*}pr_2^*Ω^0_{𝐏^{n-1}_S/S} ≅ 𝒪_Z`**: base change, the degree-zero identifications
`Ω^0 ≅ 𝒪`, and `pr_{1,*}𝒪 = 𝒪_Z`. -/
def pushforwardPullbackCoordinateBundleAmbientFormsZeroIso (n : ℕ) :
    (Scheme.Modules.pushforward
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n))).obj
        ((Scheme.Modules.pullback
          (pullback.snd (coordinateBlowupCentreToBase R m)
            (coordinateBundleAmbientToBase R n))).obj
          (Scheme.Hom.relativeDifferentialForms (coordinateBundleAmbientToBase R n)
            ((0 : ℕ) : ℤ))) ≅
      _root_.SheafOfModules.unit (coordinateBlowupCentre R m).ringCatSheaf :=
  haveI := isIso_formsDirectImageComparison_coordinateBundleProduct_zero R m n
  (Scheme.Modules.pushforward _).mapIso
      (asIso (coordinateBundleFormsBaseChange R m n 0) ≪≫
        Scheme.Hom.relativeDifferentialFormsZeroIso _ ≪≫
        (Scheme.Hom.relativeDifferentialFormsZeroIso
          (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n) ≫
            coordinateBlowupCentreToBase R m)).symm) ≪≫
    (asIso (Scheme.Hom.formsDirectImageComparison
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n))
      (coordinateBlowupCentreToBase R m) 0)).symm ≪≫
    Scheme.Hom.relativeDifferentialFormsZeroIso _

/-- The `(a, 0)` index of the product decomposition. -/
abbrev coordinateBundleTopIndex (a : ℕ) : Scheme.Hom.deRhamBoxIndex a := ⟨(a, 0), by simp⟩

/-- **The `(a, 0)` summand pushes forward to `Ω^a_{Z/S}`**:
`p_*(pr₁^*Ω^a_{Z/S} ⊗ pr₂^*Ω^0) ≅ p_*pr₂^*Ω^0 ⊗ Ω^a_{Z/S} ≅ 𝒪_Z ⊗ Ω^a_{Z/S} ≅ Ω^a_{Z/S}`, by
the symmetry of the tensor product, the projection formula and the left unitor. -/
def pushforwardCoordinateBundleFormsTopSummandIso (n a : ℕ) :
    (Scheme.Modules.pushforward
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n))).obj
        (Scheme.Hom.relativeFormsProductSummand (coordinateBlowupCentreToBase R m)
          (coordinateBundleAmbientToBase R n) a (coordinateBundleTopIndex a)) ≅
      Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (a : ℤ) :=
  (Scheme.Modules.pushforward _).mapIso
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap _ _ _) ≪≫
    Stacks.AffineProjectionFormula.pushforwardTensorPullbackIso
      (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n)) _ _ ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (coordinateBlowupCentre R m).toRingedSpace.sheaf)).mapIso
      (Iso.prod (pushforwardPullbackCoordinateBundleAmbientFormsZeroIso R m n) (Iso.refl _)) ≪≫
    AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso
      (coordinateBlowupCentre R m).toRingedSpace _

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- **`p_*Ω^a_{P/S} ≅ Ω^a_{Z/S}`** for `n ≥ 2`: the product decomposition of the forms of
`P = Z ×_S 𝐏^{n-1}_S`, pushed forward along `p`, keeps only its `(a, 0)` summand. -/
def coordinateBundleFormsPushforwardIso (a : ℕ) :
    (Scheme.Modules.pushforward (coordinateBlowupBundleToCentre R m (k + 2))).obj
        (Scheme.Hom.relativeDifferentialForms
          (coordinateBlowupBundleToCentre R m (k + 2) ≫ coordinateBlowupCentreToBase R m)
          (a : ℤ)) ≅
      Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (a : ℤ) :=
  Scheme.Hom.pushforwardFormsIsoOfIso (coordinateBundleProductIso R m (k + 2))
      (coordinateBundleProductIso_hom_comp_toCentre R m (k + 2))
      (coordinateBlowupCentreToBase R m) (a : ℤ) ≪≫
    (coordinateBundleFormsPushforwardProductIso R m (k + 2) a).symm ≪≫
    CategoryTheory.Limits.biproductIsoOfIsZero _ (coordinateBundleTopIndex a) (fun j hj =>
      isZero_pushforward_coordinateBundleFormsSummand R m k a j fun h0 => hj (Subtype.ext
        (Prod.ext (by
          have h2 : (j.1.1 : ℕ) + j.1.2 = a := j.2
          change j.1.1 = a
          omega) h0))) ≪≫
    pushforwardCoordinateBundleFormsTopSummandIso R m (k + 2) a

/-- **Clause (2) of [Stacks, Tag 0FUR] for `n ≥ 2`.** The comparison map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is a split monomorphism, because `p` has a section; its target is
isomorphic to its source (`Stacks.DeRham.coordinateBundleFormsPushforwardIso`); and
`Γ(Z, Ω^a_{Z/S})` is a finite module. So it is an isomorphism
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isSplitMono_of_iso`). -/
theorem isIso_coordinateBundleFormsDirectImage_add_two (a : ℕ) :
    IsIso (coordinateBundleFormsDirectImage R m (k + 2) a) := by
  obtain ⟨σ, hσ⟩ := Stacks.ProjectiveBundleSplitting.exists_section_projectiveSpaceOver (k + 1)
    (coordinateBlowupCentre R m)
  have := Scheme.Hom.isSplitMono_formsDirectImageComparison_of_section
    (coordinateBlowupBundleToCentre R m (k + 2)) σ hσ (coordinateBlowupCentreToBase R m) a
  have : (Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m)
      (a : ℤ)).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  have := (AlgebraicGeometry.CoherentKernel.isQuasicoherent_isFiniteType_of_isFiniteLocallyFree
    (Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (a : ℤ))).2
  have := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
    (Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (a : ℤ))
    (isAffineOpen_top _)
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isSplitMono_of_iso _
    (coordinateBundleFormsPushforwardIso R m k a)

variable (n : ℕ)

/-- **[Stacks, Tag 0FUR], clause (2).** For every ring `R`, all `m, n` and every degree
`a ≥ 0`, the canonical map `Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is an isomorphism, where `Z = 𝐀^m_S`,
`S = Spec R`, and `p : P = 𝐏^{n-1}_Z ⟶ Z`. For `n ≤ 1` the bundle is the centre itself
(`Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_of_one`; with truncated subtraction `n = 0`
gives the same bundle as `n = 1`), and `n ≥ 2` is
`Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_add_two`. -/
@[stacks 0FUR "clause (2), in the setting of Section 0FUB, \
which fixes a ring R and sets S = Spec(R), Z = A^m_S ⊂ X = A^{m+n}_S with n ≥ 1"]
theorem isIso_coordinateBundleFormsDirectImage (a : ℕ) :
    IsIso (coordinateBundleFormsDirectImage R m n a) := by
  match n with
  | 0 => exact isIso_coordinateBundleFormsDirectImage_of_one R m a
  | 1 => exact isIso_coordinateBundleFormsDirectImage_of_one R m a
  | k + 2 => exact isIso_coordinateBundleFormsDirectImage_add_two R m k a

end Stacks.DeRham
