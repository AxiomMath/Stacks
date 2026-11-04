module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedPushforwardAcyclic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFinitePushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison

/-!
# Pseudo-coherence of a finite morphism

A finite morphism of schemes `f : X ⟶ S` is pseudo-coherent exactly when the direct image
`f_*𝒪_X` of its structure sheaf is a pseudo-coherent `𝒪_S`-module, that is, when the object of
`D(𝒪_S)` it gives in degree zero is pseudo-coherent in the sense of Stacks 08CB.

## Main results

* `AlgebraicGeometry.pseudoCoherent_iff_isPseudoCoherent_pushforward_unit`: **Stacks 0AVX**, both
  directions.

## Implementation notes

The source reduces the statement to algebra, where it is Stacks 0673 for the finite ring map
`R → A`. Here the reduction is made geometrically, and the geometric translations of both halves
are already available:

1. Stacks 067Y, in the form `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`,
   replaces pseudo-coherence of `f` by relative pseudo-coherence of `𝒪_X` over `S`;
2. Stacks 09UK, `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward` — the
   scheme-level form of Stacks 0673 — moves that condition across the finite morphism `f` itself,
   taking `S` as the base and `𝟙 S` as the structure morphism of the target;
3. Stacks 09UU, `AlgebraicGeometry.Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom`
   at the identity of `S`, identifies relative pseudo-coherence over `S` with absolute
   pseudo-coherence on `S`.

What is left is the passage from `Rf_*𝒪_X` to `f_*𝒪_X`. A finite morphism is affine, so a complex
of quasi-coherent modules computes its own direct image (Stacks 0G9R, available here as
`AlgebraicGeometry.affineRightDerivedPushforward_unit_isIso`); applied to the complex
concentrated in degree zero on a quasi-coherent module this identifies `Rf_*(M[0])` with
`(f_*M)[0]`, and sheaf-level pseudo-coherence only depends on the isomorphism class of an object
of the derived category.

Pseudo-coherence is `m`-pseudo-coherence in every degree, which is
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`; the chain above is run one degree at
a time.

## References

* [The Stacks Project, Lemma 37.60.8 (0AVX)](https://stacks.math.columbia.edu/tag/0AVX)
* [The Stacks Project, Lemma 15.83.5 (0673)](https://stacks.math.columbia.edu/tag/0673)
* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Tag 09UK](https://stacks.math.columbia.edu/tag/09UK)
* [The Stacks Project, Tag 09UU](https://stacks.math.columbia.edu/tag/09UU)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Tag 0G9R](https://stacks.math.columbia.edu/tag/0G9R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- The terms of the complex concentrated in degree zero on a quasi-coherent module are
quasi-coherent: each of them is either that module or zero. -/
private theorem isQuasicoherent_singleFunctor_obj_X {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (n : ℤ) :
    (((CochainComplex.singleFunctor X.Modules 0).obj M).X n).IsQuasicoherent := by
  by_cases hn : n = 0
  · subst hn
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm inferInstance
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)

/-- A quasi-coherent module, viewed in degree zero in the derived category, has quasi-coherent
cohomology sheaves. -/
private theorem isQuasicoherent_homology_singleFunctor {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsQuasicoherent :=
  isQuasicoherent_derived_homology _ (isQuasicoherent_singleFunctor_obj_X M) i

/-- **Direct image computes derived direct image on a quasi-coherent module along an affine
morphism:** for `f : X ⟶ S` affine and `M` a quasi-coherent `𝒪_X`-module, `Rf_*(M[0])` is
`(f_*M)[0]`.

This is Stacks 0G9R at the complex concentrated in degree zero on `M`: its terms are
quasi-coherent, hence acyclic for `f_*`, so the canonical comparison from the termwise direct
image is invertible. -/
private def derivedPushforwardSingleIso {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    (schemeDerivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj M) :=
  letI K : CochainComplex X.Modules ℤ := (CochainComplex.singleFunctor X.Modules 0).obj M
  letI α := schemeDerivedPushforwardUnit f
  haveI : IsIso (α.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) :=
    affineRightDerivedPushforward_unit_isIso f (schemeDerivedPushforward f) α K
      (isQuasicoherent_singleFunctor_obj_X M)
  (schemeDerivedPushforward f).mapIso
      ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm ≪≫
    (asIso (α.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K))).symm ≪≫
    (DerivedCategory.quotientCompQhIso S.Modules).app
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward f)
        (ComplexShape.up ℤ) 0).app M)

/-- For a finite morphism `f : X ⟶ S` and an integer `m`, the structure sheaf `𝒪_X` is relatively
`m`-pseudo-coherent over `S` exactly when `f_*𝒪_X` is `m`-pseudo-coherent on `S`.

Stacks 09UK transports the relative condition along `f` itself, over the base `S`; Stacks 09UU at
the identity of `S` turns the relative condition on the target into the absolute one; and
`AlgebraicGeometry.derivedPushforwardSingleIso` replaces `Rf_*𝒪_X` by `f_*𝒪_X`. -/
private theorem isPseudoCoherentFrom_unit_iff_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) m ↔
      RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace)
        ((DerivedCategory.singleFunctor S.Modules 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) m := by
  have hrel := Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward f f (𝟙 S)
    (Category.comp_id f)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
    (isQuasicoherent_homology_singleFunctor _) m
  have habs := Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom f (𝟙 S)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) m
  exact hrel.trans (habs.trans
    ⟨fun h => h.of_iso (derivedPushforwardSingleIso f _),
      fun h => h.of_iso (derivedPushforwardSingleIso f _).symm⟩)

/-- **Stacks 0AVX.** A finite morphism of schemes `f : X ⟶ S` is pseudo-coherent if and only if
the direct image `f_*𝒪_X` of its structure sheaf is a pseudo-coherent `𝒪_S`-module, that is, if
and only if the object of `D(𝒪_S)` it determines in degree zero is pseudo-coherent. -/
@[stacks 0AVX]
public theorem pseudoCoherent_iff_isPseudoCoherent_pushforward_unit {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] :
    PseudoCoherent f ↔
      RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
        ((DerivedCategory.singleFunctor S.Modules 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h := (pseudoCoherent_iff_isModulePseudoCoherent f).mp hf
    refine (RingedSpace.isPseudoCoherent_iff_forall (X := S.toRingedSpace) _).2 fun m => ?_
    exact (isPseudoCoherentFrom_unit_iff_pushforward f m).mp (h.choose_spec m)
  · refine (pseudoCoherent_iff_isModulePseudoCoherent f).mpr ⟨inferInstance, fun m => ?_⟩
    exact (isPseudoCoherentFrom_unit_iff_pushforward f m).mpr
      ((RingedSpace.isPseudoCoherent_iff_forall (X := S.toRingedSpace) _).1 hf m)

end AlgebraicGeometry

end
