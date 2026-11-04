module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.FiniteFreeComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealFreeModelBasis
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion

/-!
# Every affine open carries a bounded-above finite free model

Let `X` be a scheme and let `𝒦` be a pseudo-coherent complex of `𝒪_X`-modules. This file
constructs, over every affine open `U` of `X`, a term of `AlgebraicGeometry.DerivedFreeModel 𝒦 U`:
the local situation that the hypothesis of [Stacks, Tag 0ESP] describes is realized on every affine
open, which is the sentence "such local free resolutions exist" of the source's proof.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 08EE](https://stacks.math.columbia.edu/tag/08EE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry

noncomputable section

universe u w w'

namespace Scheme.Modules

/-- The two spellings of the restriction of a complex of `𝒪_X`-modules to an open subscheme: the
pushforward along the functor on opens, which is the idiom of Stacks 08CB, and Mathlib's
restriction along the open immersion `U.ι`. -/
def ringedSpaceRestrictComplexIso (X : Scheme.{u}) (U : X.Opens)
    (C : CochainComplex X.Modules ℤ) :
    RingedSpace.restrictComplex (X := X.toRingedSpace) C U ≅ restrictComplex C U :=
  have : (RingedSpace.restrictModules X.toRingedSpace U).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext _ _; rfl⟩
  have : (show StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤
        StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding) from
      restrictFunctor U.ι).PreservesZeroMorphisms := ⟨fun _ _ ↦ by ext _ _; rfl⟩
  (NatIso.mapHomologicalComplex (RingedSpace.restrictModulesIsoRestrictFunctor X U)
    (ComplexShape.up ℤ)).app C

/-- Restricting to `⊤` and then back along `AlgebraicGeometry.Scheme.topIso` is the identity. -/
def restrictFunctorTopIso (Y : Scheme.{u}) :
    restrictFunctor (⊤ : Y.Opens).ι ⋙ restrictFunctor Y.topIso.inv ≅ 𝟭 Y.Modules :=
  (restrictFunctorComp Y.topIso.inv (⊤ : Y.Opens).ι).symm ≪≫
    restrictFunctorCongr Y.topIso.inv_hom_id ≪≫ restrictFunctorId

/-- **An object of `D(𝒪_Y)` is recovered from its restriction to `⊤`.** Restriction to `⊤` is
exact, so it descends to the derived categories, and composing it with the restriction along
`AlgebraicGeometry.Scheme.topIso` gives back the identity. -/
def qRestrictTopIso (Y : Scheme.{u}) [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w'} (⊤ : Y.Opens).toScheme.Modules]
    (C : CochainComplex Y.Modules ℤ) :
    DerivedCategory.Q.obj C ≅
      (restrictFunctor Y.topIso.inv).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (restrictComplex C (⊤ : Y.Opens))) :=
  DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (restrictFunctorTopIso Y) (ComplexShape.up ℤ)).app C).symm ≪≫
    ((restrictFunctor Y.topIso.inv).mapDerivedCategoryFactors.app
      (restrictComplex C (⊤ : Y.Opens))).symm

end Scheme.Modules

/-- The restriction of a pseudo-coherent complex of `𝒪_X`-modules to an open is pseudo-coherent. -/
private theorem isPseudoCoherentComplex_restrictComplex {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPseudoCoherentComplex (X := X.toRingedSpace) K) (U : X.Opens) :
    RingedSpace.IsPseudoCoherentComplex (X := (U.toScheme).toRingedSpace)
      (RingedSpace.restrictComplex (X := X.toRingedSpace) K U) :=
  fun m => RingedSpace.isPseudoCoherentComplexFrom_restrictComplex K m (hK m) U

/-- **A pseudo-coherent complex of `𝒪_Y`-modules on an affine scheme is isomorphic, in `D(𝒪_Y)`,
to a bounded-above complex of finite free `𝒪_Y`-modules.**

This is [Stacks, Tag 08EE], `AlgebraicGeometry.exists_boundedAbove_finiteFree_lift`, at the open
`⊤`: there the complex produced lives on the ambient affine scheme and the comparison is read
after restricting to the given open, so the comparison is transported back along
`AlgebraicGeometry.Scheme.Modules.qRestrictTopIso`. -/
theorem exists_freeComplex_of_isAffine (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} Y.Modules] (K : CochainComplex Y.Modules ℤ)
    (hK : RingedSpace.IsPseudoCoherentComplex (X := Y.toRingedSpace) K) :
    ∃ P : CochainComplex Y.Modules ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, ∃ I : Type u, Finite I ∧ Nonempty (P.X i ≅ SheafOfModules.free I)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K) := by
  let : HasDerivedCategory.{u} ((⊤ : Y.Opens).toScheme.Modules) :=
    inferInstanceAs (HasDerivedCategory.{u}
      (StrictlyPerfect.OXMod.{u, u} (Y.toRingedSpace.restrict (⊤ : Y.Opens).isOpenEmbedding)))
  have hpc : RingedSpace.IsPseudoCoherent
      (X := Y.toRingedSpace.restrict (⊤ : Y.Opens).isOpenEmbedding)
      (DerivedCategory.Q.obj (RingedSpace.restrictComplex (X := Y.toRingedSpace) K ⊤)) :=
    ⟨RingedSpace.restrictComplex (X := Y.toRingedSpace) K ⊤,
      isPseudoCoherentComplex_restrictComplex K hK ⊤,
      ⟨Iso.refl _⟩⟩
  obtain ⟨P, hPb, hPfree, ⟨eP⟩⟩ :=
    exists_boundedAbove_finiteFree_lift Y ⊤ (isAffineOpen_top Y).isCompact _ hpc
  refine ⟨P, hPb, hPfree, ⟨Scheme.Modules.qRestrictTopIso Y P ≪≫
    (Scheme.Modules.restrictFunctor Y.topIso.inv).mapDerivedCategory.mapIso ?_ ≪≫
    (Scheme.Modules.qRestrictTopIso Y K).symm⟩⟩
  exact DerivedCategory.Q.mapIso
      (Scheme.Modules.ringedSpaceRestrictComplexIso Y ⊤ P).symm ≪≫ eP ≪≫
    DerivedCategory.Q.mapIso (Scheme.Modules.ringedSpaceRestrictComplexIso Y ⊤ K)

/-- **Every affine open of a scheme carries a bounded-above finite free model of a pseudo-coherent
complex of `𝒪_X`-modules.** This is the sentence "such local free resolutions exist" of the proof
of [Stacks, Tag 0ESP], so that the local situation its statement describes is realized on every
affine open.

The complex of finite free `𝒪_U`-modules comes from
`AlgebraicGeometry.exists_freeComplex_of_isAffine`; the modelling complex of `𝒪_X`-modules is its
pushforward along `U.ι`, whose restriction to `U` is the complex itself by the counit
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` of the adjunction, and whose
sections over `U` are therefore given bases by
`AlgebraicGeometry.Scheme.Modules.exists_basis_pair_of_isoFree`. The ranks are cut off above a
degree where the complex vanishes: a free module on an empty index type is a zero object, so the
trivialization still holds there. -/
theorem nonempty_freeModel_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPseudoCoherentComplex (X := X.toRingedSpace) K) :
    Nonempty (DerivedFreeModel K U) := by
  classical
  have : IsAffine (U.toScheme) := hU
  let : HasDerivedCategory.{u + 1} ((U.toScheme).Modules) := HasDerivedCategory.standard _
  obtain ⟨P, ⟨b, hb⟩, hPfree, ⟨eP⟩⟩ := exists_freeComplex_of_isAffine (U.toScheme)
    (RingedSpace.restrictComplex (X := X.toRingedSpace) K U)
    (isPseudoCoherentComplex_restrictComplex K hK U)
  choose I hIfin hIiso using hPfree
  let Md : CochainComplex X.Modules ℤ :=
    ((Scheme.Modules.pushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let rk : ℤ → ℕ := fun i => if b < i then 0 else Nat.card (I i)
  have hfree : ∀ i : ℤ, Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj (Md.X i) ≅
      SheafOfModules.free (R := (U.toScheme).ringCatSheaf) (ULift.{u} (Fin (rk i)))) := by
    intro i
    have hcounit : (Scheme.Modules.restrictFunctor U.ι).obj (Md.X i) ≅ P.X i :=
      (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app (P.X i)
    by_cases hi : b < i
    · have hempty : IsEmpty (ULift.{u} (Fin (rk i))) := by
        rw [show rk i = 0 from if_pos hi]
        exact inferInstanceAs (IsEmpty (ULift.{u} (Fin 0)))
      have hz : IsZero (SheafOfModules.free (R := (U.toScheme).ringCatSheaf)
          (ULift.{u} (Fin (rk i)))) := by
        rw [IsZero.iff_id_eq_zero]
        exact (SheafOfModules.free (R := (U.toScheme).ringCatSheaf)
          (ULift.{u} (Fin (rk i)))).freeHomEquiv.injective
          (funext fun j => (hempty.false j).elim)
      exact ⟨((hb i hi).of_iso hcounit).iso hz⟩
    · have := hIfin i
      refine ⟨hcounit ≪≫ (hIiso i).some ≪≫ SheafOfModules.freeFunctor.mapIso ?_⟩
      rw [show rk i = Nat.card (I i) from if_neg hi]
      exact ((Finite.equivFin (I i)).trans (Equiv.ulift.{u}).symm).toIso
  choose bas _bas' _hbas using fun i : ℤ =>
    Scheme.Modules.exists_basis_pair_of_isoFree (Md.X i) U (hfree i) (W := ⊤) (W' := ⊤)
      le_rfl U U U.ι_image_top U.ι_image_top le_rfl
  exact ⟨{ model := Md
           rank := rk
           top := b
           rank_eq_zero_of_top_lt := fun i hi => if_pos hi
           isFree := hfree
           basis := bas
           derivedIso := ⟨DerivedCategory.Q.mapIso
             ((NatIso.mapHomologicalComplex
               (Scheme.Modules.restrictFunctorAdjCounitIso U.ι) (ComplexShape.up ℤ)).app P) ≪≫
             eP ≪≫ DerivedCategory.Q.mapIso
               (Scheme.Modules.ringedSpaceRestrictComplexIso X U K)⟩ }⟩

end

end AlgebraicGeometry

end
