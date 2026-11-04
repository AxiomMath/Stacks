module

public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic

/-!
# Quasi-coherent modules on an affine scheme as modules over its global sections

For an affine scheme `X` this file identifies modules of finite presentation on `X` with finitely
presented `Γ(X, ⊤)`-modules: a fully faithful functor
`Stacks.AlgebraicGeometry.AffineTilde.tildeOf X : ModuleCat Γ(X, ⊤) ⥤ X.Modules`, the statement
that every module of finite presentation is in its image, and its compatibility with pullback
along a morphism of affine schemes.

Mathlib has all three for `X = Spec R`: `AlgebraicGeometry.tilde.functor R` is fully faithful,
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` recognises its image, and
the pullback compatibility is `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`. Here
they are transported from `Spec Γ(X, ⊤)` to `X` along `AlgebraicGeometry.Scheme.isoSpec`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`: pullback along an isomorphism of schemes
  is an equivalence of module categories.
* `Stacks.AlgebraicGeometry.AffineTilde.tildeOf`: `M ↦ M~`, read on an affine scheme rather than
  on a spectrum.
* `Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIso`: `f^*(M~) ≅ (Γ(X) ⊗ M)~` for a
  morphism `f` of affine schemes, naturally in `M`.
* `Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIsoApp`: the same, one module at a time and
  with no composite of functors in its type.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`: pullback along an
  isomorphism of schemes is an equivalence.
* `Stacks.AlgebraicGeometry.AffineTilde.exists_iso_tildeOf`: every module of finite presentation
  on an affine scheme is `M~` for a finitely presented module of global sections.

## Implementation notes

`tildeOf X` is `tilde.functor Γ(X, ⊤)` followed by pullback along `X.isoSpec.hom`.  Full
faithfulness is therefore inherited: the first factor is fully faithful in Mathlib and the second
is an equivalence.  That `pullback f` is an equivalence for `f` an isomorphism is not in Mathlib
and is not found by instance search, since `AlgebraicGeometry.Scheme.Modules.pullback` is defined
as a left adjoint; it is supplied here by exhibiting the quasi-inverse `pullback f⁻¹` and the two
unit and counit isomorphisms as composites of `pullbackComp`, `pullbackCongr` and `pullbackId`,
with `CategoryTheory.Equivalence.mk` repairing the unit so that no triangle identity has to be
checked by hand.

The pullback compatibility is assembled from Mathlib's `pullbackComp`, the naturality of
`AlgebraicGeometry.Scheme.isoSpec` and `tildePullbackIso`.  It is *not* proved compatible with
composition of morphisms of affine schemes: that coherence would be a statement about
`tildePullbackIso`, which is constructed by uniqueness of left adjoints, and is not available.

## References

* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along an isomorphism of schemes is an equivalence of the categories of sheaves of
modules. -/
noncomputable def pullbackEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((pullbackId Y).symm ≪≫ pullbackCongr e.inv_hom_id.symm ≪≫ (pullbackComp e.inv e.hom).symm)
    (pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId X)

/-- Pullback along an isomorphism of schemes is an equivalence of the categories of sheaves of
modules. -/
instance isEquivalence_pullback_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (Scheme.Modules.pullback f).IsEquivalence := by
  have h : (pullbackEquivOfIso (asIso f)).functor = Scheme.Modules.pullback f := rfl
  exact h ▸ (pullbackEquivOfIso (asIso f)).isEquivalence_functor

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.AffineTilde

open Scheme.Modules

/-- The module associated to a module of global sections, on an affine scheme rather than on a
spectrum: `tilde.functor Γ(X, ⊤)` transported along `AlgebraicGeometry.Scheme.isoSpec`. -/
noncomputable def tildeOf (X : Scheme.{u}) [IsAffine X] : ModuleCat.{u} Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom

/-- The functor `tildeOf X` is full. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] : (tildeOf X).Full := by
  unfold tildeOf; infer_instance

/-- The functor `tildeOf X` is faithful. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] : (tildeOf X).Faithful := by
  unfold tildeOf; infer_instance

/-- Pulling back `M~` along a morphism of affine schemes gives the module associated to the base
change of `M` along the induced map of global sections, naturally in `M`. -/
noncomputable def tildeOfPullbackIso {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    tildeOf Y ⋙ Scheme.Modules.pullback f ≅
      ModuleCat.extendScalars (Scheme.Hom.appTop f).hom ⋙ tildeOf X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(Y, ⊤))
      (pullbackComp f Y.isoSpec.hom ≪≫
        pullbackCongr (Scheme.isoSpec_hom_naturality f).symm ≪≫
        (pullbackComp X.isoSpec.hom (Spec.map (Scheme.Hom.appTop f))).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso
      (Scheme.Hom.appTop f)) (Scheme.Modules.pullback X.isoSpec.hom) ≪≫
    Functor.associator _ _ _

/-- The component of `tildeOfPullbackIso` at a module `M`: `f^*(M~) ≅ (Γ(X) ⊗ M)~`, with the
source and target written without a composite of functors. -/
noncomputable def tildeOfPullbackIsoApp {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (M : ModuleCat.{u} Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).obj ((tildeOf Y).obj M) ≅
      (tildeOf X).obj ((ModuleCat.extendScalars (Scheme.Hom.appTop f).hom).obj M) :=
  (tildeOfPullbackIso f).app M

/-- The isomorphisms `tildeOfPullbackIsoApp f M` are natural in the module `M`. -/
lemma tildeOfPullbackIsoApp_naturality {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    {M N : ModuleCat.{u} Γ(Y, ⊤)} (v : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((tildeOf Y).map v) ≫ (tildeOfPullbackIsoApp f N).hom
      = (tildeOfPullbackIsoApp f M).hom ≫
        (tildeOf X).map ((ModuleCat.extendScalars (Scheme.Hom.appTop f).hom).map v) :=
  (tildeOfPullbackIso f).hom.naturality v

/-- Every sheaf of modules of finite presentation on an affine scheme is the module associated to
a finitely presented module of global sections. -/
theorem exists_iso_tildeOf (X : Scheme.{u}) [IsAffine X] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ M : ModuleCat.{u} Γ(X, ⊤), Module.FinitePresentation Γ(X, ⊤) M ∧
      Nonempty ((tildeOf X).obj M ≅ F) := by
  let F' : (Spec Γ(X, ⊤)).Modules := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  have hF' : F'.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ F
  have hqc : F'.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F'
    exact σ.isQuasicoherent
  have hiso : IsIso (Scheme.Modules.fromTildeΓ F') :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ F' hqc
  let M : ModuleCat.{u} Γ(X, ⊤) := moduleSpecΓFunctor.obj F'
  let eF' : (tilde.functor Γ(X, ⊤)).obj M ≅ F' :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F') hiso
  have : ((tilde.functor Γ(X, ⊤)).obj M).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso eF'.symm hF'
  refine ⟨M, (tilde_isFinitePresentation_iff M).mp ‹_›, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback X.isoSpec.hom).mapIso eF' ≪≫
    (pullbackEquivOfIso X.isoSpec).counitIso.app F

end Stacks.AlgebraicGeometry.AffineTilde

end
