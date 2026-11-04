module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over an affine base

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S` affine. For
a quasi-coherent `𝒪_X`-module `F` the cohomology of `F` and the global sections of its higher
direct images agree,
$$ H^q(X, F) \;=\; H^0(S, R^qf_*F), $$
and the identification is natural in `F`.

Both sides are modules over `Γ(S, 𝒪_S)`: the left one by restriction of scalars along
`f^\#  : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, the right one because `R^qf_*F` is a sheaf on `S`. The
identification is an isomorphism of the two functors on the category of quasi-coherent modules.

## Main definitions

* `Stacks.Cohomology.AffineBase.pushforwardSectionsIso`: sections of a direct image over the
  whole of `S` are the global sections of the source, as `Γ(S, 𝒪_S)`-modules.
* `Stacks.Cohomology.AffineBase.sectionsRightDerivedPushforwardIso`: the comparison in a
  natural-number degree.
* `Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward`: the comparison in
  every integer degree, which is [Stacks, Tag 01XK].

## Main results

* `Stacks.Cohomology.AffineBase.rightAcyclic_sectionsFunctor_of_isQuasicoherent`: on an affine
  scheme a quasi-coherent module is right acyclic for global sections (Serre vanishing,
  [Stacks, Tag 01XB]).
* `Stacks.Cohomology.AffineBase.preservesLeftHomologyOf_pushforward_injectiveResolution`:
  global sections on `S` preserve the homology of the direct image of an injective resolution of
  a quasi-coherent module.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

/-- **The quasi-coherent modules of a scheme**, as a full subcategory of `X.Modules`. -/
abbrev quasicoherentInclusion (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-! ### Global sections over an affine base -/

/-- **Sections of a direct image over the whole base are the global sections of the source.**
For `f : X ⟶ S`, the `Γ(S, 𝒪_S)`-module `Γ(S, f_*F)` is `Γ(X, F)` with its scalars restricted
along `f^\# : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, and the identification is the identity on sections. -/
def pushforwardSectionsIso (f : X ⟶ S) :
    Scheme.Modules.pushforward f ⋙ sectionsFunctor S ⊤ ≅
      sectionsFunctor X ⊤ ⋙ ModuleCat.restrictScalars f.appTop.hom :=
  Iso.refl _

/-- **Serre vanishing as right acyclicity.** A quasi-coherent module on an affine scheme is
right acyclic for global sections. -/
theorem rightAcyclic_sectionsFunctor_of_isQuasicoherent (S : Scheme.{u}) [IsAffine S]
    (F : S.Modules) [F.IsQuasicoherent] : (sectionsFunctor S ⊤).rightAcyclic F := by
  refine (rightAcyclic_iff_isZero_rightDerived (sectionsFunctor S ⊤) F).2 fun p hp ↦ ?_
  have hAb : IsZero (((sectionsFunctor S ⊤ ⋙
      forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).rightDerived p).obj F) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F ⊤ (isAffineOpen_top S) p hp
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (hAb.of_iso (((sectionsFunctor S ⊤).rightDerivedCompIso
      (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}) p).app F).symm))

/-! ### Exactness of global sections on a pushed-forward injective resolution -/

section Comparison

variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]

/-- **Global sections on an affine base are exact on the direct image of an injective
resolution of a quasi-coherent module.** For `f : X ⟶ S` quasi-compact and quasi-separated
with `S` affine and `A` a quasi-coherent `𝒪_X`-module, global sections on `S` preserve the left
homology of the short complex in degree `n` of the direct image of the injective resolution of
`A`. -/
theorem preservesLeftHomologyOf_pushforward_injectiveResolution (n : ℕ)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (sectionsFunctor S ⊤).PreservesLeftHomologyOf
      ((((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution ((quasicoherentInclusion X).obj A)).cocomplex).sc n) := by
  have hqc : ((quasicoherentInclusion X).obj A).IsQuasicoherent := A.property
  set I := injectiveResolution ((quasicoherentInclusion X).obj A)
  refine ((sectionsFunctor S ⊤).rightAcyclic_cycles_and_preservesLeftHomologyOf_sc _
    (fun i ↦ ?_) (fun i ↦ ?_) n).2
  · exact Stacks.SchemeCohomology.rightAcyclic_schemePushforward_obj f ⊤ _ (I.injective i)
  · have := Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived f
      ((quasicoherentInclusion X).obj A) i
    exact (sectionsFunctor S ⊤).rightAcyclic.prop_of_iso
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) i)
      (rightAcyclic_sectionsFunctor_of_isQuasicoherent S
        (((Scheme.Modules.pushforward f).rightDerived i).obj
          ((quasicoherentInclusion X).obj A)))

/-- **The comparison in a natural-number degree.** `H^n(X, -)`, as a module over
`Γ(S, 𝒪_S)`, is the global sections of `R^nf_*(-)` on the quasi-coherent modules. -/
def sectionsRightDerivedPushforwardIso (n : ℕ) :
    quasicoherentInclusion X ⋙
        (sectionsFunctor X ⊤).rightDerived n ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      quasicoherentInclusion X ⋙
        (Scheme.Modules.pushforward f).rightDerived n ⋙ sectionsFunctor S ⊤ :=
  have : (ModuleCat.restrictScalars f.appTop.hom).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars f.appTop.hom
  Functor.isoWhiskerLeft (quasicoherentInclusion X)
      (((sectionsFunctor X ⊤).rightDerivedCompIso
        (ModuleCat.restrictScalars f.appTop.hom) n).symm ≪≫
      Functor.rightDerivedIsoOfNatIso (pushforwardSectionsIso f).symm n) ≪≫
    (Functor.rightDerivedCompIsoOfPreservesLeftHomology (quasicoherentInclusion X)
      (Scheme.Modules.pushforward f) (sectionsFunctor S ⊤) n
      (preservesLeftHomologyOf_pushforward_injectiveResolution f n)).symm

/-- Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes with `S` affine. For every `q : ℤ` the cohomology `H^q(X, F)` of a quasi-coherent
`𝒪_X`-module `F`, regarded as a `Γ(S, 𝒪_S)`-module by restriction of scalars along
`f^\# : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, is the module of global sections of the higher direct image
`R^qf_*F`, naturally in `F`. -/
@[stacks 01XK, ega "III 1.4.14" "affine base, Z=point"]
def cohomologyIsoSectionsRightDerivedPushforward (q : ℤ) :
    quasicoherentInclusion X ⋙
        (sectionsFunctor X ⊤).rightDerivedPlus q ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      quasicoherentInclusion X ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus q ⋙ sectionsFunctor S ⊤ := by
  by_cases hq : 0 ≤ q
  · rw [show q = (q.toNat : ℤ) from (Int.toNat_of_nonneg hq).symm]
    exact Functor.isoWhiskerLeft (quasicoherentInclusion X)
        (Functor.isoWhiskerRight
          (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X ⊤) q.toNat).symm
          (ModuleCat.restrictScalars f.appTop.hom)) ≪≫
      sectionsRightDerivedPushforwardIso f q.toNat ≪≫
      Functor.isoWhiskerLeft (quasicoherentInclusion X)
        (Functor.isoWhiskerRight
          (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q.toNat)
          (sectionsFunctor S ⊤))
  · refine NatIso.ofComponents (fun A ↦ IsZero.iso
      ((ModuleCat.restrictScalars f.appTop.hom).map_isZero
        (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj (sectionsFunctor X ⊤) q
          (by omega) _))
      ((sectionsFunctor S ⊤).map_isZero
        (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
          (Scheme.Modules.pushforward f) q (by omega) _))) (fun {A B} g ↦ ?_)
    exact ((sectionsFunctor S ⊤).map_isZero
      (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
        (Scheme.Modules.pushforward f) q (by omega) _)).eq_of_tgt _ _

end Comparison

end Stacks.Cohomology.AffineBase

end
