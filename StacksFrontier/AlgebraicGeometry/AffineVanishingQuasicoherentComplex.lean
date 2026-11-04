module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded.Tower
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf

/-!
# Affine vanishing for a complex with quasi-coherent cohomology

Let `X = Spec R` be an affine scheme and let `K` be a cochain complex of `𝒪_X`-modules. Derived
global sections `RΓ(X, -)` is computed by applying `Γ(X, -)` termwise to a K-injective resolution
of `K`; whether that already agrees with `Γ(X, K)` is the content of [Stacks, Tag 08D4] at
`N = 1`, and for an unbounded complex it is not formal. Two instances of it are settled here, both
stated *without* any derived category, so that they can be read at any `HasDerivedCategory` model:

* termwise global sections inverts every K-injective resolution of the degreewise sheafification
  `M̃^•` of a complex of `R`-modules — this is the hypothesis of
  `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso`, so it is
  the invertibility of the unit of the derived Spec–Γ adjunction of [Stacks, Tag 06Z0];
* if the global sections of a K-injective resolution of a complex with quasi-coherent cohomology
  are acyclic, then the complex itself is acyclic — that is, `RΓ(X, -)` has zero kernel on
  `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde` — unbounded affine vanishing for the
  complexes `M̃^•`.
* `AlgebraicGeometry.isZero_homology_of_isZero_homology_globalSectionsOver` — derived global
  sections detects the zero object among the complexes with quasi-coherent cohomology.
* `Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_Q_map_iff`,
  `Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_Qh_quot_map_iff`,
  `Stacks.SmallDerivedCategory.isIso_Qh_quot_map`,
  `Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj` and
  `Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero` — the translations between
  the derived category and complexes that make a model-free statement possible.

## Implementation notes

**Why the argument happens at `CategoryTheory.HasDerivedCategory.standard`.** The input is
[Stacks, Tag 08D4], formalized as
`isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` and
`isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus`, both in the
`AlgebraicGeometry` namespace, in
`StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/UpperBounds.lean`, whose own input —
the truncation-tower convergence of [Stacks, Tag 08D3], resting on [Stacks, Tag 0D6P] — is
available only at that model. `HasDerivedCategory` carries the localized category as data, so a
statement proved there says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` at which `AlgebraicGeometry.derivedTilde`
and `AlgebraicGeometry.derivedGlobalSectionsOver` are stated. The cure taken here is not to
re-bind the convergence chain but to pass through statements mentioning no derived category at
all: `Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff` turns invertibility of
the structure map of *any* right derived functor along the quasi-isomorphisms into the assertion
that the functor inverts one K-injective resolution, which is a statement about complexes. Both
main results below have that shape, and
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean` reads them back at the
locally small model.

`attribute [local instance 10000] HasDerivedCategory.standard` is needed rather than a plain
`attribute [local instance]`: this file imports the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, `SheafOfModules.hasDerivedCategory` and
`ModuleCat.hasDerivedCategory`, and at equal priority instance search picks the first two for the
sheaf categories while picking `standard` for `ModuleCat`, which would put the two sides of
`RΓ(X, -)` at different models.

**Visibility and names.** Outside the `Stacks.SmallDerivedCategory` section, the public
declarations are the two main results and the pieces that
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/EventualExtVanishing.lean` and
`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveSpaceDirectImage/TwistCohomology.lean` reuse:
`homSecs`, `derSecs`, `derSecsUnit`, the instances on `secsOver` and `homSecs`, and
`isZero_rightDerivedPlus_gam`. The
other declarations are `private`: each mentions the standard-model derived category of
`𝒪_X`-modules, which a consumer at the locally small model cannot use. The names are abbreviated
accordingly: `secsOver` is
`AlgebraicGeometry.globalSectionsOver` with its source spelled
`SheafOfModules X.ringCatSheaf` rather than `AlgebraicGeometry.Scheme.Modules` — the spelling
[Stacks, Tag 08D4] is stated in, the two types being definitionally equal but carrying separately
declared `Category` and `Preadditive` instances, so that the crossing has to be a type-ascribed
definition as in `StacksFrontier/AlgebraicGeometry/DerivedQCoh/TildeFactorization.lean` — and
`homSecs`, `derSecs`, `derSecsUnit` are its homotopy-category form, its unbounded total right
derived functor and the structure map of that derived functor.

**The two bounds of 08D4 are both cited, not reproved.**
`AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι` and
`isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus` are stated
for an arbitrary abelian target, so `isIso_homologyFunctor_dGam_map_truncLEι` and
`isIso_homologyFunctor_dGam_map_truncGEπ` below are one-line specializations of them at
`ModuleCat R`.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.SmallDerivedCategory

/-! ### Model-independent reformulations -/

/-- **`Hⁱ` of the image of a morphism of complexes in the derived category is invertible exactly
when the morphism is a quasi-isomorphism in degree `i`.** The localization functor `Q` factors the
cohomology functors of the derived category through the cohomology of complexes, so the two
assertions correspond. This is the translation that lets a statement proved at one
`HasDerivedCategory` model be read at another. -/
public theorem isIso_homologyFunctor_map_Q_map_iff {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C i).map (DerivedCategory.Q.map φ)) ↔
      QuasiIsoAt φ i := by
  rw [show (DerivedCategory.homologyFunctor C i).map (DerivedCategory.Q.map φ) =
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C i).map φ from rfl,
    NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i),
    quasiIsoAt_iff_isIso_homologyMap]
  rfl

/-- The criterion of `Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_Q_map_iff` for the
localization read through the homotopy category. -/
public theorem isIso_homologyFunctor_map_Qh_quot_map_iff {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C i).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ))) ↔ QuasiIsoAt φ i := by
  rw [show (DerivedCategory.homologyFunctor C i).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) =
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor C i).map φ from rfl,
    NatIso.isIso_map_iff (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      (DerivedCategory.homologyFunctor C i))]
  exact isIso_homologyFunctor_map_Q_map_iff φ i

/-- **A quasi-isomorphism becomes invertible in the derived category**, read through the homotopy
category. -/
public theorem isIso_Qh_quot_map {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (hφ : QuasiIso φ) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) := by
  have := hφ
  rw [show DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map φ from rfl,
    NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C)]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) φ).2 inferInstance

/-- **An object of the derived category with vanishing cohomology is zero.** The zero endomorphism
is invertible on every cohomology object, hence invertible, hence equal to the identity. -/
public theorem isZero_of_isZero_homologyFunctor_obj {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (X : DerivedCategory C)
    (h : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj X)) : IsZero X := by
  have hiso : IsIso (0 : X ⟶ X) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [Functor.map_zero]
    exact ⟨⟨0, (h n).eq_of_src _ _, (h n).eq_of_src _ _⟩⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : X ⟶ X), comp_zero]

/-- **The cohomology objects of the zero object vanish**, the cohomology functors being
additive. -/
public theorem isZero_homologyFunctor_obj_of_isZero {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {X : DerivedCategory C} (h : IsZero X) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj X) := by
  rw [IsZero.iff_id_eq_zero, ← (DerivedCategory.homologyFunctor C n).map_id,
    h.eq_of_src (𝟙 X) 0, Functor.map_zero]

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

open Stacks.SmallDerivedCategory

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `secsOver f` preserves finite limits, being `globalSectionsOver f` (whose definition and
`Additive` instance live in `StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf`). -/
public instance : PreservesFiniteLimits (secsOver f) :=
  inferInstanceAs (PreservesFiniteLimits (globalSectionsOver f))
/-- `secsOver f` preserves products indexed by `ℕ`, being `globalSectionsOver f`. -/
public instance : PreservesLimitsOfShape (Discrete ℕ) (secsOver f) :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (globalSectionsOver f))
/-- `secsOver f` has a pointwise right derived functor on the bounded-below homotopy category,
read in `D⁺(A)`. -/
public instance : ((secsOver f).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} X.ringCatSheaf)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).hasPointwiseRightDerivedFunctor

/-- Termwise global sections over `Spec A` on the homotopy category of complexes of
`𝒪_X`-modules, followed by the localization functor to `D(A)`. -/
public abbrev homSecs : HomotopyCategory (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⥤
    DerivedCategory (ModuleCat.{u} A) :=
  (secsOver f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `homSecs f` has a total right derived functor along the quasi-isomorphisms. -/
public instance : (homSecs f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- The unbounded derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, at the standard model of
the derived category: the total right derived functor of `homSecs f`. -/
public abbrev derSecs : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
    DerivedCategory (ModuleCat.{u} A) :=
  (homSecs f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The structure map `homSecs f ⟶ Qh ⋙ derSecs f` of the total right derived functor. -/
public abbrev derSecsUnit : homSecs f ⟶ DerivedCategory.Qh ⋙ derSecs f :=
  (homSecs f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- Termwise global sections on the homotopy category, read in `D(A)`, is termwise global
sections followed by localization. -/
private def secsFactors :
    HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⋙
        homSecs f ≅
      (secsOver f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((secsOver f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

variable {K L : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ}

private theorem isIso_homGam_map_quot_map_iff (φ : K ⟶ L) :
    IsIso ((homSecs f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ)) ↔
      QuasiIso (((secsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  rw [show (homSecs f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ homSecs f).map φ from rfl,
    NatIso.isIso_map_iff (secsFactors f)]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} A) _

private theorem isIso_homologyFunctor_homGam_map_quot_map_iff (φ : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((homSecs f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ))) ↔
      QuasiIsoAt (((secsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i := by
  rw [show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((homSecs f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ)) =
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ homSecs f) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ from rfl,
    NatIso.isIso_map_iff (Functor.isoWhiskerRight (secsFactors f)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i))]
  exact isIso_homologyFunctor_map_Q_map_iff _ i

/-! ### Serre vanishing and the two bounds of Stacks 08D4 -/

/-- **Serre vanishing in the form needed for 08D4.** On an affine scheme, the higher right
derived functors of `secsOver f` vanish on a quasi-coherent module. -/
public theorem isZero_rightDerivedPlus_gam [IsAffine X] (M : SheafOfModules.{u} X.ringCatSheaf)
    (hM : M.IsQuasicoherent) (p : ℤ) (hp : 0 < p) :
    IsZero (((secsOver f).rightDerivedPlus p).obj M) := by
  have hac : (secsOver f).rightAcyclic M := by
    refine (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived (secsOver f) M).2 fun q hq => ?_
    have := hM
    exact isZero_rightDerived_globalSectionsOver_of_isQuasicoherent f M q hq
  exact ((CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (secsOver f) M).2 inferInstance).1 hac p hp

private theorem isIso_dGamUnit_app_isKInjective
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (hI : I.IsKInjective) :
    IsIso ((derSecsUnit f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective (secsOver f) (derSecs f)
    (derSecsUnit f) Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso I hI

private theorem isIso_homologyFunctor_dGam_map_truncGEπ [IsAffine X]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derSecs f).map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) := by
  have h := isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus
    X (secsOver f) (derSecs f) (derSecsUnit f) 1
    (fun M hM p hp => isZero_rightDerivedPlus_gam f M hM p (by exact_mod_cast hp))
    E hE i i le_rfl
  have e : i - ((1 : ℕ) : ℤ) + 1 = i := by push_cast; ring
  rw [e] at h
  exact h

private theorem isIso_homologyFunctor_dGam_map_truncLEι
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derSecs f).map ((DerivedCategory.TStructure.t.truncLEι i).app E))) :=
  -- `secsOver f` is spelled with source `SheafOfModules X.ringCatSheaf`, whose `Preadditive`
  -- instance is declared separately from that of the definitionally equal `X.Modules` the
  -- library statement uses, so the additivity instance is transferred across by ascription.
  @isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι X _ _ _ _ _ (secsOver f)
    (inferInstanceAs (secsOver f).Additive) (derSecs f) (derSecsUnit f)
    (inferInstanceAs ((derSecs f).IsRightDerivedFunctor (derSecsUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))))
    E hE i i le_rfl

/-! ### The bounded below case -/

private theorem quasiIso_gam_map_of_plus [IsAffine X]
    (M : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hM : CochainComplex.plus _ M) (hqc : ∀ n : ℤ, (M.X n).IsQuasicoherent)
    {I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ} (s : M ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((secsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
  (isIso_globalSectionsComplexComparison_iff f s hI hs).1
    (isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent f M hM hqc)

private theorem isIso_dGamUnit_app_of_plus [IsAffine X]
    (M : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hM : CochainComplex.plus _ M) (hqc : ∀ n : ℤ, (M.X n).IsQuasicoherent) :
    IsIso ((derSecsUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) := by
  obtain ⟨I, s, hI, hs⟩ :=
    Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
      (C := SheafOfModules.{u} X.ringCatSheaf) M
  refine (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (A := SheafOfModules.{u} X.ringCatSheaf)
    Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso (homSecs f) (derSecs f)
    (derSecsUnit f) s hI hs).2 ?_
  exact (isIso_homGam_map_quot_map_iff f s).2 (quasiIso_gam_map_of_plus f M hM hqc s hI hs)

/-! ### The factorization through the truncation -/

/-- The cohomology of a complex, read in the derived category. -/
private def homologyFunctorObjQhQuotIso (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (n : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} X.ringCatSheaf) n).app K

private theorem isIso_homologyFunctor_dGam_map_Qh_quot_map [IsAffine X]
    {K L : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ} (i : ℤ)
    (hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent) (hL : L.IsStrictlyGE i)
    (π : K ⟶ L) (hπ : ∀ j : ℤ, i ≤ j → QuasiIsoAt π j) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derSecs f).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map π)))) := by
  have := hL
  set P := SheafOfModules.isQuasicoherent X.ringCatSheaf with hP
  set E := DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
      (ComplexShape.up ℤ)).obj K) with hEdef
  set EL := DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
      (ComplexShape.up ℤ)).obj L) with hELdef
  have hE : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) n).obj E) := by
    intro n
    exact P.prop_of_iso (homologyFunctorObjQhQuotIso K n).symm (hK n)
  have hGE : EL.IsGE i :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app L).symm i
  set u := DerivedCategory.Qh.map
    ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
      (ComplexShape.up ℤ)).map π) with hu
  have hfac : (DerivedCategory.TStructure.t.truncGEπ i).app E ≫
      DerivedCategory.TStructure.t.descTruncGE u i = u :=
    DerivedCategory.TStructure.t.π_descTruncGE u i
  have hg : IsIso (DerivedCategory.TStructure.t.descTruncGE u i) := by
    rw [DerivedCategory.isIso_iff]
    intro j
    rcases le_or_gt i j with hj | hj
    · have h1 : IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} X.ringCatSheaf) j).map
            ((DerivedCategory.TStructure.t.truncGEπ i).app E)) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ i j hj E
      have h2 : IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} X.ringCatSheaf) j).map u) :=
        (isIso_homologyFunctor_map_Qh_quot_map_iff π j).2 (hπ j hj)
      have h3 : IsIso ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} X.ringCatSheaf) j).map
              ((DerivedCategory.TStructure.t.truncGEπ i).app E) ≫
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
            (DerivedCategory.TStructure.t.descTruncGE u i)) := by
        rw [← Functor.map_comp, hfac]
        exact h2
      exact IsIso.of_isIso_comp_left
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
          ((DerivedCategory.TStructure.t.truncGEπ i).app E)) _
    · have hz1 : IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} X.ringCatSheaf) j).obj
            ((DerivedCategory.TStructure.t.truncGE i).obj E)) :=
        ((DerivedCategory.TStructure.t.truncGE i).obj E).isZero_of_isGE i j hj
      have hz2 : IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} X.ringCatSheaf) j).obj EL) := EL.isZero_of_isGE i j hj
      exact ⟨⟨0, hz1.eq_of_src _ _, hz2.eq_of_src _ _⟩⟩
  have h4 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derSecs f).map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) :=
    isIso_homologyFunctor_dGam_map_truncGEπ f E hE i
  have := hg
  rw [← hfac, Functor.map_comp, Functor.map_comp]
  infer_instance

/-! ### Unbounded affine vanishing -/

private theorem isIso_dGamUnit_app_of_truncations [IsAffine X]
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent)
    (hdata : ∀ i : ℤ, ∃ (L : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
      (π : K ⟶ L), L.IsStrictlyGE i ∧ (∀ n : ℤ, (L.X n).IsQuasicoherent) ∧
      (∀ j : ℤ, i ≤ j → QuasiIsoAt π j) ∧
      QuasiIsoAt (((secsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map π) i) :
    IsIso ((derSecsUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  obtain ⟨L, π, hL, hLqc, hπ, hΓπ⟩ := hdata i
  have hnat := (derSecsUnit f).naturality
    ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
      (ComplexShape.up ℤ)).map π)
  have ha : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((homSecs f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map π))) :=
    (isIso_homologyFunctor_homGam_map_quot_map_iff f π i).2 hΓπ
  have hb : IsIso ((derSecsUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
    isIso_dGamUnit_app_of_plus f L ⟨i, hL⟩ hLqc
  have hd : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derSecs f).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map π)))) :=
    isIso_homologyFunctor_dGam_map_Qh_quot_map f i hK hL π hπ
  have key : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((derSecsUnit f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((DerivedCategory.Qh ⋙ derSecs f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map π))) := by
    rw [← Functor.map_comp, ← hnat, Functor.map_comp]
    infer_instance
  have hd' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.Qh ⋙ derSecs f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map π))) := hd
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.Qh ⋙ derSecs f).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ)).map π)))

/-! ### The affine case -/

/-- The terms of the degreewise sheafification of a complex of `R`-modules are quasi-coherent. -/
private theorem isQuasicoherent_X_tilde (R : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).X n).IsQuasicoherent :=
  inferInstanceAs ((tilde.functor R).obj (M.X n)).IsQuasicoherent

/-- The cohomology sheaves of the degreewise sheafification of a complex of `R`-modules are
quasi-coherent: the terms are, and quasi-coherence is closed under kernels and cokernels. -/
private theorem isQuasicoherent_homology_tilde (R : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homology
      n).IsQuasicoherent :=
  Stacks.DerivedQCoh.prop_homology (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (isQuasicoherent_X_tilde R M) n

/-- **Unbounded affine vanishing for the complexes `M̃^•`, [Stacks, Tag 08D4] at `N = 1`.** Let
`M^•` be a cochain complex of `R`-modules and let `s : M̃^• ⟶ I` be a quasi-isomorphism into a
K-injective complex of `𝒪_{Spec R}`-modules. Then `Γ(Spec R, s)` is again a quasi-isomorphism: the
complex of global sections of `M̃^•` — which is `M^•` itself — already computes
`RΓ(Spec R, M̃^•)`.

By `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` this is
exactly the invertibility of the unit of the derived Spec–Γ adjunction of [Stacks, Tag 06Z0].

The proof is the source's: the comparison `Hⁱ(RΓ(Spec R, -))` of `M̃^•` with the sheafified
truncation `(τ_{≥ i}M)^~` is an isomorphism by [Stacks, Tag 08D4] part (2), the truncation is
bounded below with quasi-coherent terms so Leray's acyclicity lemma computes its derived global
sections termwise, and `Γ ∘ (-)^~` is the identity. No derived category occurs in the statement,
which is what lets it be read at the locally small model; see the implementation notes. -/
public theorem quasiIso_globalSectionsOver_map_tilde (R : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    {I : CochainComplex (Spec R).Modules ℤ}
    (s : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  have hunit : IsIso ((derSecsUnit (𝟙 (Spec R))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
    refine isIso_dGamUnit_app_of_truncations (𝟙 (Spec R)) _
      (fun n => isQuasicoherent_homology_tilde R M n) fun i => ?_
    have h1 : CochainComplex.IsStrictlyGE
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (M.truncGE i)) i :=
      inferInstance
    have h2 : ∀ n : ℤ, ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (M.truncGE i)).X n).IsQuasicoherent :=
      isQuasicoherent_X_tilde R _
    have h3 : ∀ j : ℤ, i ≤ j → QuasiIsoAt
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE i)) j := by
      intro j hj
      have := M.quasiIsoAt_πTruncGE i j hj
      infer_instance
    exact ⟨_, _, h1, h2, h3,
      quasiIsoAt_globalSectionsOver_map_tilde_map_πTruncGE R M i i le_rfl⟩
  exact (isIso_homGam_map_quot_map_iff (𝟙 (Spec R)) s).1
    ((Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
      (A := SheafOfModules.{u} (Spec R).ringCatSheaf)
      Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
      (homSecs (𝟙 (Spec R))) (derSecs (𝟙 (Spec R))) (derSecsUnit (𝟙 (Spec R))) s hI hs).1 hunit)

/-! ### Derived global sections detects the zero object -/

/-- The image of a complex under `RΓ` at the standard model is the complex of global sections of
any K-injective resolution. -/
private def derSecsObjIso {K I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    (derSecs f).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((secsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  haveI := isIso_Qh_quot_map s hs
  haveI := isIso_dGamUnit_app_isKInjective f I hI
  (derSecs f).mapIso (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
    (asIso ((derSecsUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (secsFactors f).app I

/-- At the standard model, `H^i(RΓ(Spec R, M^~[-i]))` is `M`. -/
private def homologySecsSingleIso (R : CommRingCat.{u}) (i : ℤ) (N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((derSecs (𝟙 (Spec R))).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Spec R).ringCatSheaf) i).obj ((tilde.functor R).obj N))) ≅ N := by
  set Scx : CochainComplex (SheafOfModules.{u} (Spec R).ringCatSheaf) ℤ :=
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj N) with hScx
  have hterm : ∀ n : ℤ, (Scx.X n).IsQuasicoherent := isQuasicoherent_X_tilde R _
  have h0 : CochainComplex.IsStrictlyGE
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj N) i := inferInstance
  have hS : Scx.IsStrictlyGE i := by
    rw [hScx]
    exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (tilde.functor R)
      i).2 h0
  haveI hL := isIso_dGamUnit_app_of_plus (𝟙 (Spec R)) Scx ⟨i, hS⟩ hterm
  haveI : IsIso ((tildeGlobalSectionsComplexUnit R).app
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj N)) := NatIso.isIso_app_of_isIso _ _
  let eSingle : (CochainComplex.singleFunctor (SheafOfModules.{u} (Spec R).ringCatSheaf) i).obj
      ((tilde.functor R).obj N) ≅ Scx :=
    ((HomologicalComplex.singleMapHomologicalComplex (tilde.functor R)
      (ComplexShape.up ℤ) i).app N).symm
  let e1 : (DerivedCategory.singleFunctor (SheafOfModules.{u} (Spec R).ringCatSheaf) i).obj
        ((tilde.functor R).obj N) ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Scx) :=
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (Spec R).ringCatSheaf) i).app _ ≪≫
      DerivedCategory.Q.mapIso eSingle ≪≫
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (Spec R).ringCatSheaf)).app
        Scx).symm
  let e2 : (derSecs (𝟙 (Spec R))).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Scx)) ≅
      DerivedCategory.Q.obj
        (((secsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj Scx) :=
    (asIso ((derSecsUnit (𝟙 (Spec R))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Scx))).symm ≪≫
      (secsFactors (𝟙 (Spec R))).app Scx
  let e3 : ((secsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj Scx ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj N :=
    (asIso ((tildeGlobalSectionsComplexUnit R).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj N))).symm
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((derSecs (𝟙 (Spec R))).mapIso e1 ≪≫ e2 ≪≫ DerivedCategory.Q.mapIso e3 ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) i).app N).symm) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).app N

/-- **Derived global sections detects the zero object on an affine scheme.** Let `K` be a cochain
complex of `𝒪_{Spec R}`-modules whose cohomology sheaves are all quasi-coherent, and let
`s : K ⟶ I` be a quasi-isomorphism into a K-injective complex. If the complex of global sections
`Γ(Spec R, I)` — which computes `RΓ(Spec R, Q K)` — is acyclic, then `K` is acyclic.

This is the kernel-vanishing hypothesis of [Stacks, Tag 09J1] for `RΓ(Spec R, -)` on
`D_QCoh(𝒪_{Spec R})`, and it is what upgrades full faithfulness of derived sheafification to an
equivalence. It is read off `Hⁱ(RΓ(Spec R, E)) ≅ Γ(Spec R, Hⁱ(E))`: the two truncation comparisons
of [Stacks, Tag 08D4] identify `Hⁱ(RΓ(E))` with `Hⁱ(RΓ(τ_{≥ i}τ_{≤ i}E))`, that object is a single
quasi-coherent module `M^~` in degree `i`, and Leray's acyclicity lemma computes its derived global
sections as `M`. A quasi-coherent module with vanishing global sections is zero, `(-)^~` being an
equivalence onto the quasi-coherent modules. -/
public theorem isZero_homology_of_isZero_homology_globalSectionsOver (R : CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} (Spec R).ringCatSheaf) ℤ)
    (hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent)
    {I : CochainComplex (SheafOfModules.{u} (Spec R).ringCatSheaf) ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s)
    (hac : ∀ n : ℤ, IsZero ((((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology n)) (i : ℤ) :
    IsZero (K.homology i) := by
  set P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf with hP
  set E := DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Spec R).ringCatSheaf)
      (ComplexShape.up ℤ)).obj K) with hEdef
  have hE : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Spec R).ringCatSheaf) n).obj E) := fun n =>
    P.prop_of_iso (homologyFunctorObjQhQuotIso K n).symm (hK n)
  -- `H^i(RΓ(E)) = 0`
  have hz0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derSecs (𝟙 (Spec R))).obj E)) := by
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (derSecsObjIso (𝟙 (Spec R)) s hI hs))
    exact IsZero.of_iso (hac i)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _)
  -- truncate from above
  have h1 := isIso_homologyFunctor_dGam_map_truncLEι (𝟙 (Spec R)) E hE i
  have hz1 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derSecs (𝟙 (Spec R))).obj ((DerivedCategory.TStructure.t.truncLE i).obj E))) :=
    IsZero.of_iso hz0 (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derSecs (𝟙 (Spec R))).map ((DerivedCategory.TStructure.t.truncLEι i).app E))))
  have hE₁ : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Spec R).ringCatSheaf) n).obj
        ((DerivedCategory.TStructure.t.truncLE i).obj E)) := fun n =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj P E hE i n
  -- truncate from below
  have h2 := isIso_homologyFunctor_dGam_map_truncGEπ (𝟙 (Spec R))
    ((DerivedCategory.TStructure.t.truncLE i).obj E) hE₁ i
  have hz2 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derSecs (𝟙 (Spec R))).obj ((DerivedCategory.TStructure.t.truncGE i).obj
        ((DerivedCategory.TStructure.t.truncLE i).obj E)))) :=
    IsZero.of_iso hz1 (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derSecs (𝟙 (Spec R))).map ((DerivedCategory.TStructure.t.truncGEπ i).app
        ((DerivedCategory.TStructure.t.truncLE i).obj E))))).symm
  -- the doubly truncated object is a single quasi-coherent module
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((DerivedCategory.TStructure.t.truncGE i).obj
      ((DerivedCategory.TStructure.t.truncLE i).obj E)) i
  have hg2 := DerivedCategory.isIso_homologyFunctor_map_truncGEπ i i le_rfl
    ((DerivedCategory.TStructure.t.truncLE i).obj E)
  have hl1 := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι E i i le_rfl
  have eY : Y ≅ K.homology i :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (Spec R).ringCatSheaf) i).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (Spec R).ringCatSheaf) i).mapIso
        e.symm ≪≫
      (asIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Spec R).ringCatSheaf) i).map
          ((DerivedCategory.TStructure.t.truncGEπ i).app
            ((DerivedCategory.TStructure.t.truncLE i).obj E)))).symm ≪≫
      asIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Spec R).ringCatSheaf) i).map
          ((DerivedCategory.TStructure.t.truncLEι i).app E)) ≪≫
        homologyFunctorObjQhQuotIso K i
  have hY : P Y := P.prop_of_iso eY.symm (hK i)
  obtain ⟨N, ⟨eN⟩⟩ : (tilde.functor R).essImage Y := by
    rw [essImage_tilde]
    exact hY
  have hz3 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derSecs (𝟙 (Spec R))).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Spec R).ringCatSheaf) i).obj ((tilde.functor R).obj N)))) :=
    IsZero.of_iso hz2 ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((derSecs (𝟙 (Spec R))).mapIso (e ≪≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Spec R).ringCatSheaf) i).mapIso eN.symm))).symm
  have hzN : IsZero N := IsZero.of_iso hz3 (homologySecsSingleIso R i N).symm
  have hz4 : IsZero ((tilde.functor R).obj N) := by
    rw [IsZero.iff_id_eq_zero, ← (tilde.functor R).map_id,
      hzN.eq_of_src (𝟙 N) 0, (tilde.functor R).map_zero]
  exact IsZero.of_iso (IsZero.of_iso hz4 eN.symm) eY.symm

end AlgebraicGeometry

end
