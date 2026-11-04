module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechComplexRepresentsSupport
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardFromDisjointOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing

/-!
# Derived sections with support invert the augmentation (Stacks 0G7M)

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions and let `Z` be their
common zero locus, the complement of `⋃ᵢ X.basicOpen fᵢ`.  For a quasi-coherent `𝒪_X`-module
`F`, Stacks 0G7M says that the extended alternating Čech complex `𝓕^•` of Stacks 0G7I
represents `i_* R𝓗_Z(F)`, the comparison being the augmentation `𝓕^• ⟶ F[0]` of Stacks 0G7L.

The half of that statement which uses the quasi-coherence of `F` is that `R𝓗_Z` inverts the
augmentation; it is proved here, and combined with the other half — the acyclicity of `𝓕^•`
over `X ∖ Z` of Stacks 0G7K — to give the conclusion of Stacks 0G7M itself, and the vanishing
of the local cohomology sheaves above degree `c` that Stacks 0G7N reads off it.  The argument
for the first half is the one of the source.  Each positive-degree term of the complex is
`(U_{i₀…i_p} → X)_* (F|_{U_{i₀…i_p}})`, for `U_{i₀…i_p}` an intersection of principal opens of
the equations; that intersection is the principal open of the product of the equations, so its
inclusion is affine, so the higher direct images of the quasi-coherent `F|_{U_{i₀…i_p}}` along
it vanish (Stacks 01XC) and the term is its own derived direct image; since `U_{i₀…i_p}` is
disjoint from `Z`, the term is therefore killed by `R𝓗_Z` (Stacks 0G73).  That is exactly the
hypothesis under which
`Stacks.Perfect.CechAugmentation.isIso_map_augmentation_of_isZero_obj_single_restrictedModule`
concludes that `R𝓗_Z` inverts the augmentation.

## Main definitions

* `equationsClosedSet`: the common zero locus of the equations, as a subset of `X`.
* `schemeSupportedSectionsFunctor`: the functor of sections supported on a closed subset of a
  scheme, read on `X.Modules`.

## Main results

* `isIso_map_augmentation_of_isQuasicoherent`: **a derived functor of sections supported on the
  common zero locus of `f₁, …, f_c` inverts the augmentation of Stacks 0G7L, for every
  quasi-coherent coefficient module**.
* `isIso_derivedSupportedSectionsOnClosed_map_augmentation`: the same for the chosen total right
  derived functor `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed`.
* `isZero_obj_single_restrictedModule`: that derived functor kills each positive-degree term of
  the extended alternating Čech complex, for any closed subset of the zero locus.
* `equationsOpen_eq_basicOpen_prod` and `isAffineHom_equationsOpen_ι`: an intersection of the
  principal opens of the equations is the principal open of their product, so its inclusion is
  an affine morphism.
* `nonempty_rightDerived_obj_single_iso`: Leray's acyclicity lemma in degree zero — a total
  right derived functor sends a right acyclic object in degree `0` to its image in degree `0`.
* `nonempty_cechIso_derivedSupportedSections`: **Stacks 0G7M**, the extended alternating Čech
  complex represents `i_* R𝓗_Z(F)`.
* `isZero_homology_derivedSupportedSections_of_gt`: the local cohomology sheaves `ℋ ^i_Z(F)`
  vanish for `i > c`, for a closed subset cut out by `c` *global* equations.

## Implementation notes

The derived functor `R𝓗_Z` enters as a parameter: a functor between unbounded derived categories
together with a comparison transformation exhibiting it as a right derived functor of
`schemeSupportedSectionsFunctor`.  This is the shape in which Stacks 0G73 is stated in this
library, and it keeps the statements independent of a choice of derived functor;
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed` is one such choice.

The underlying ringed space of an open subscheme of `X` is the restriction of the underlying
ringed space of `X`, and the scheme-level and ringed-space-level direct images along the
inclusion agree, both definitionally.  So Stacks 01XC, stated for schemes, and Stacks 0G73,
stated for ringed spaces, compose with no transport.  The source category of `R𝓗_Z` is however
written as `X.Modules` rather than as the sheaves of modules on the underlying ringed space:
`X.Modules` is the spelling used by Stacks 0G7I and Stacks 0G7L, and
`schemeSupportedSectionsFunctor` exists to supply it, since the two spellings — being
definitionally equal but not syntactically so — are not interchangeable for instance resolution.

Passing from the vanishing of the higher direct images to the identification of a term with its
derived direct image is Leray's acyclicity lemma, in the form
`Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`, compared with the unbounded derived
functor by `Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`.

## References

* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0G73](https://stacks.math.columbia.edu/tag/0G73)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechDerivedSupport

attribute [local instance] HasDerivedCategory.standard

/-! ### A right derived functor on a single complex of a right acyclic object -/

section Generic

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **Leray's acyclicity lemma in degree zero.**  If an object `M` is right acyclic for an
additive functor `G`, then a total right derived functor of `G` sends `M` placed in degree `0`
to `G(M)` placed in degree `0`. -/
public theorem nonempty_rightDerived_obj_single_iso
    (G : A ⥤ B) [G.Additive] [EnoughInjectives A]
    [(G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (M : A) (hacyclic : G.rightAcyclic M) :
    Nonempty (RG.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      (DerivedCategory.singleFunctor B 0).obj (G.obj M)) := by
  let E : DerivedCategory.Plus A := (DerivedCategory.Plus.singleFunctor A 0).obj M
  let eE : E.obj ≅ (DerivedCategory.singleFunctor A 0).obj M :=
    (DerivedCategory.Plus.singleFunctorιIso A 0).app M
  have hE : E.obj.IsGE 0 := (DerivedCategory.Plus.isGE_ι_obj_iff E 0).2 inferInstance
  obtain ⟨eR⟩ :=
    Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus G RG β hcomp E 0 hE
  let J := (HomotopyCategory.Plus.singleFunctor A 0).obj M
  have hunit : IsIso (G.rightDerivedFunctorPlusUnit.app J) := hacyclic
  let eRF : G.rightDerivedFunctorPlus.obj E ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (G.obj M) :=
    G.rightDerivedFunctorPlus.mapIso ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).app M) ≪≫
      (asIso (G.rightDerivedFunctorPlusUnit.app J)).symm ≪≫
      (Functor.mapSingleFunctorCompQhIso G).app M
  exact ⟨RG.mapIso eE.symm ≪≫ eR ≪≫ DerivedCategory.Plus.ι.mapIso eRF ≪≫
    (DerivedCategory.Plus.singleFunctorιIso B 0).app (G.obj M)⟩

end Generic

/-! ### Stacks 0G73 with the derived-functor hypotheses taken explicitly -/

/-- **Stacks 0G73**, with the two hypotheses that a functor is a right derived functor taken as
explicit arguments rather than as instances.

This is the form in which Stacks 0G73 is applied to a scheme below: the category of modules on a
scheme and the category of modules on its underlying ringed space are definitionally equal but
written differently, and an instance stated for one spelling is not found for the other, whereas
an explicit argument is checked up to definitional equality. -/
private theorem isZero_obj_derivedPushforward (Y : RingedSpace.{u, u}) (Z : Set Y.carrier)
    (hZ : IsClosed Z) (U : TopologicalSpace.Opens Y.carrier)
    (hUZ : (U : Set Y.carrier) ∩ Z = ∅)
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Y.restrict U.isOpenEmbedding))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (αj : (modulePushforward (Y.ofRestrict U.isOpenEmbedding)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing (Y.restrict U.isOpenEmbedding))) (ComplexShape.up ℤ)))
    (RH : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace Y Z))))
    (αH : (supportedSectionsOnClosedFunctor Y Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor αH (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Y.restrict U.isOpenEmbedding)))) :
    IsZero (RH.obj (Rj.obj K)) :=
  let _ := hRj
  let _ := hRH
  isZero_derivedSupportedSections_derivedPushforward Y Z hZ U hUZ Rj αj RH αH K

/-! ### Sections supported on a closed subset of a scheme -/

/-- The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on a closed subset `Z` of a
scheme `X`, with source the category `X.Modules` of modules on `X` as a scheme.

This is `Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor` of the
underlying ringed space of `X`; the two categories of modules are definitionally the same, and
the point of the re-ascription is to make the spelling used by Stacks 0G7I and Stacks 0G7L
available to instance resolution. -/
public def schemeSupportedSectionsFunctor (X : Scheme.{u}) (Z : Set X) (hZ : IsClosed Z) :
    X.Modules ⥤
      SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z)) :=
  supportedSectionsOnClosedFunctor X.toRingedSpace Z hZ

/-- `H_Z` is additive, being right adjoint to the additive pushforward along the inclusion
of `Z`. -/
public instance schemeSupportedSectionsFunctor_additive (X : Scheme.{u}) (Z : Set X)
    (hZ : IsClosed Z) : (schemeSupportedSectionsFunctor X Z hZ).Additive :=
  inferInstanceAs (supportedSectionsOnClosedFunctor X.toRingedSpace Z hZ).Additive

/-- `H_Z` preserves finite limits, being a right adjoint. -/
public instance schemeSupportedSectionsFunctor_preservesFiniteLimits (X : Scheme.{u})
    (Z : Set X) (hZ : IsClosed Z) :
    PreservesFiniteLimits (schemeSupportedSectionsFunctor X Z hZ) := by
  have := (modulePushforward_supportedSectionsOnClosed_adjunction X.toRingedSpace Z
    hZ).rightAdjoint_preservesLimits
  exact inferInstanceAs
    (PreservesFiniteLimits (supportedSectionsOnClosedFunctor X.toRingedSpace Z hZ))

/-! ### The principal intersections and the common zero locus -/

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- The intersection of the principal opens belonging to an increasing tuple of indices is the
principal open of the product of the corresponding equations. -/
public theorem equationsOpen_eq_basicOpen_prod {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    equationsOpen f p s = X.basicOpen (∏ k, f (s.1 k)) := by
  induction p with
  | zero => simp [equationsOpen]
  | succ p ih =>
      rw [equationsOpen, Stacks.Cohomology.AffineVanishing.iInf_fin_succ_eq]
      let st : CechCochains.OrdIndex (I := Fin c) p :=
        ⟨fun k => s.1 k.succ, s.2.comp Fin.strictMono_succ⟩
      show X.basicOpen (f (s.1 0)) ⊓ equationsOpen f p st = _
      rw [ih st]
      simp [st, Fin.prod_univ_succ, Scheme.basicOpen_mul]

/-- The inclusion of an intersection of the principal opens of the equations is an affine
morphism: that intersection is the principal open of the product of the equations. -/
public instance isAffineHom_equationsOpen_ι {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    IsAffineHom (equationsOpen f p s).ι := by
  rw [equationsOpen_eq_basicOpen_prod f s]
  infer_instance

/-- Every intersection of the principal opens of the equations is contained in their union. -/
public theorem equationsOpen_le_iSup_basicOpen {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    equationsOpen f p s ≤ ⨆ i, X.basicOpen (f i) := by
  rw [equationsOpen]
  exact (iInf_le _ 0).trans (le_iSup_of_le (s.1 0) le_rfl)

/-- The common zero locus of a finite family of global equations: the complement of the union of
the principal opens on which the equations are invertible.  This is the underlying set of the
closed subscheme they cut out, as in Stacks 0G7I. -/
public def equationsClosedSet : Set X := ((⨆ i, X.basicOpen (f i) : X.Opens) : Set X)ᶜ

/-- The common zero locus of the equations is closed. -/
public theorem isClosed_equationsClosedSet : IsClosed (equationsClosedSet f) :=
  (⨆ i, X.basicOpen (f i) : X.Opens).isOpen.isClosed_compl

/-- The common zero locus of the equations is the image of the closed subscheme they cut out,
the closed subscheme of Stacks 0G7I. -/
public theorem equationsClosedSet_eq_range_subschemeι :
    equationsClosedSet f =
      Set.range (Scheme.IdealSheafData.ofIdealTop (equationsIdeal f)).subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_ofIdealTop]
  ext x
  rw [equationsIdeal, Scheme.zeroLocus_span]
  simp [equationsClosedSet, Scheme.zeroLocus_def]

/-- An intersection of the principal opens of the equations is disjoint from every subset of
the common zero locus. -/
public theorem equationsOpen_inter_eq_empty {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) {Z : Set X} (hZ : Z ⊆ equationsClosedSet f) :
    ((equationsOpen f p s : X.Opens) : Set X) ∩ Z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨hxU, hxZ⟩ =>
    hZ hxZ (equationsOpen_le_iSup_basicOpen f s hxU)

/-! ### `R𝓗_Z` kills the positive-degree terms -/

/-- **Stacks Project, Tag 0G7M**, the step of the proof that uses quasi-coherence.  Let `Z` be a
closed subset of `X` contained in the common zero locus of `f₁, …, f_c`.  Then a derived functor
of sections supported on `Z` kills the direct image `(U_{i₀…i_p} → X)_* (F|_{U_{i₀…i_p}})` of a
quasi-coherent module `F`, placed in degree `0`.

The inclusion of `U_{i₀…i_p}` is affine, so the higher direct images of the quasi-coherent
`F|_{U_{i₀…i_p}}` along it vanish by [Stacks, Tag 01XC] and the direct image is its own derived
direct image; `U_{i₀…i_p}` is disjoint from `Z`, so [Stacks, Tag 0G73] applies. -/
public theorem isZero_obj_single_restrictedModule (F : X.Modules) [F.IsQuasicoherent]
    {Z : Set X} (hZ : IsClosed Z) (hZsub : Z ⊆ equationsClosedSet f) {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p)
    (RH : DerivedCategory X.Modules ⥤
      DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))))
    (αH : (schemeSupportedSectionsFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor αH (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsZero (RH.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
      (restrictedModule f F p s))) := by
  let j := modulePushforward
    (X.toRingedSpace.ofRestrict (equationsOpen f p s).isOpenEmbedding)
  let M := (Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).obj F
  -- a total right derived functor of `j` on unbounded derived categories
  have hres : ∀ K : CochainComplex (SheafOfModules.{u}
        (structureSheafRing (X.toRingedSpace.restrict (equationsOpen f p s).isOpenEmbedding))) ℤ,
      ∃ (I : CochainComplex _ ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q := fun K =>
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K
  let _ : (j.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (structureSheafRing (X.toRingedSpace.restrict (equationsOpen f p s).isOpenEmbedding)))
          (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} _ hres).1
  let Rj := (j.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αj := (j.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  have hcompj : ∀ I : CochainComplex _ ℤ, I.IsKInjective →
      IsIso (αj.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := fun I hI =>
    Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective j Rj αj hres I hI
  -- `M` is right acyclic for `j`: the inclusion is affine and `M` is quasi-coherent
  let _ : (j.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso _) :=
    HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso _
  let _ : (j.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso _) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  obtain ⟨eK⟩ := nonempty_rightDerived_obj_single_iso j Rj αj hcompj M
    (((j.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 inferInstance).2 fun i hi =>
      Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom
        (equationsOpen f p s).ι M i hi)
  -- Stacks 0G73: `R𝓗_Z` kills a derived direct image from an open disjoint from `Z`
  have hvan : IsZero (RH.obj (Rj.obj ((DerivedCategory.singleFunctor _ 0).obj M))) :=
    isZero_obj_derivedPushforward X.toRingedSpace Z hZ
      (equationsOpen f p s) (equationsOpen_inter_eq_empty f s hZsub) Rj αj inferInstance RH αH
      (inferInstanceAs (RH.IsRightDerivedFunctor αH
        (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))) _
  exact (hvan.of_iso (RH.mapIso eK).symm).of_iso
    (RH.mapIso ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      (j.mapIso ((Scheme.Modules.restrictFunctorIsoPullback (equationsOpen f p s).ι).app F)))).symm

/-! ### The augmentation is inverted -/

/-- **Stacks Project, Tag 0G7M**, the step of the proof that uses the quasi-coherence of the
coefficient module.  With `X`, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `F` as in Stacks 0G7I, and `F`
quasi-coherent, **a derived functor `R𝓗_Z` of sections supported on the common zero locus `Z` of
the equations inverts the augmentation `𝓕^• ⟶ F[0]` of Stacks 0G7L**.

The augmentation is the comparison between the extended alternating Čech complex and its
coefficient module, so this says that the complex and the module have the same derived sections
with support on `Z`. -/
@[stacks 0G7M "the derived sections with support invert the augmentation"]
public theorem isIso_map_augmentation_of_isQuasicoherent (F : X.Modules) [F.IsQuasicoherent]
    (RH : DerivedCategory X.Modules ⥤
      DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f)))))
    (αH : (schemeSupportedSectionsFunctor X (equationsClosedSet f)
        (isClosed_equationsClosedSet f)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor αH
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))) :
    IsIso (RH.map (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F)) :=
  let _ := hRH
  Stacks.Perfect.CechAugmentation.isIso_map_augmentation_of_isZero_obj_single_restrictedModule
    f F (schemeSupportedSectionsFunctor X (equationsClosedSet f)
      (isClosed_equationsClosedSet f)) RH αH fun _ s =>
    isZero_obj_single_restrictedModule f F (isClosed_equationsClosedSet f) le_rfl s RH αH

/-- **Stacks Project, Tag 0G7M**, the step of the proof that uses quasi-coherence, for the
total right derived functor `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed`
of sections supported on the common zero locus of the equations. -/
public theorem isIso_derivedSupportedSectionsOnClosed_map_augmentation (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)).map
        (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F)) :=
  isIso_map_augmentation_of_isQuasicoherent f F
    (derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f))
    (derivedSupportedSectionsOnClosedUnit X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f))
    (inferInstanceAs ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)).IsRightDerivedFunctor
        (derivedSupportedSectionsOnClosedUnit X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ))))

/-! ### The complex represents the derived sections with support -/

/-- **Stacks Project, Tag 0G7M.**  With `X`, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `F` as in Stacks 0G7I
and `F` quasi-coherent, the extended alternating Čech complex `𝓕^•` **represents
`i_* R𝓗_Z(F)`**, the comparison being the augmentation `𝓕^• ⟶ F[0]` of Stacks 0G7L.

Two halves combine.  The augmentation is inverted by `R𝓗_Z`, which is
`isIso_derivedSupportedSectionsOnClosed_map_augmentation` and is where quasi-coherence is used;
and `𝓕^•` is its own derived sections with support, which is
`Stacks.Perfect.CechSupportRepresentation.nonempty_pushforwardDerivedSupportCechIso` and is
where the acyclicity of Stacks 0G7K is used.  The K-injective resolution entering the second
half is not canonical, so the conclusion is stated as the existence of the isomorphism, in the
form the neighbouring existence statements of Stacks 0A3B take. -/
@[stacks 0G7M "the extended alternating Čech complex represents i_*RℋZ(F)"]
public theorem nonempty_cechIso_derivedSupportedSections (F : X.Modules) [F.IsQuasicoherent] :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
    letI := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)
    Nonempty
      (DerivedCategory.Q.obj
          ((Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech f F).complex.extend
            ComplexShape.embeddingUpNat) ≅
        (modulePushforward (closedSubsetInclusion X.toRingedSpace
            (equationsClosedSet f))).mapDerivedCategory.obj
          ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
              (isClosed_equationsClosedSet f)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  obtain ⟨e⟩ :=
    Stacks.Perfect.CechSupportRepresentation.nonempty_pushforwardDerivedSupportCechIso
      (Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech f F)
      (isClosed_equationsClosedSet f) (TopologicalSpace.Opens.ext (compl_compl _))
  exact ⟨e.symm ≪≫ (modulePushforward (closedSubsetInclusion X.toRingedSpace
    (equationsClosedSet f))).mapDerivedCategory.mapIso
      (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsOnClosed_map_augmentation f F))⟩

/-- **Stacks Project, Tag 0G7N for global equations.**  If the closed subset `Z` is the common
zero locus of `c` global functions on `X`, then the local cohomology sheaves of a quasi-coherent
`𝒪_X`-module vanish above degree `c`:

`ℋ ^i_Z(F) = 0` for `i > c`.

By Stacks 0G7M the object `i_* R𝓗_Z(F)` is the extended alternating Čech complex, whose terms —
indexed by the strictly increasing tuples in `{1, …, c}` — vanish above degree `c`; and `i_*` is
exact and fully faithful, so it detects the vanishing. -/
public theorem isZero_homology_derivedSupportedSections_of_gt (F : X.Modules)
    [F.IsQuasicoherent] (i : ℤ) (hi : (c : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace
            (equationsClosedSet f)))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  obtain ⟨e⟩ := nonempty_cechIso_derivedSupportedSections f F
  refine Stacks.Perfect.DerivedSupportedSectionsValue.isZero_of_isZero_modulePushforward
    X.toRingedSpace (equationsClosedSet f) (isClosed_equationsClosedSet f) _ ?_
  refine IsZero.of_iso ?_ ((exactFunctorDerivedHomologyIso
    (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))) i).app
      ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors X.Modules i).app _)
  exact Stacks.Perfect.CechSupportRepresentation.isZero_homology_extend_of_gt
    (Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech f F) hi

end Stacks.Perfect.CechDerivedSupport

end
