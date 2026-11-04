module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback

/-!
# Objects of `D_QCoh` on a representable algebraic space, and relative pseudo-coherence

Let `S` be a scheme and let `f : X → Y` be a morphism of representable algebraic spaces over
`S` which is locally of finite type, represented by a morphism of schemes `f₀ : X₀ → Y₀`. Stacks
Remark 0CSW makes three assertions:

1. `f₀` is locally of finite type;
2. every object `E` of `D_QCoh(𝒪_X)` is the pullback of a unique object `E₀` of
   `D_QCoh(𝒪_{X₀})`, by Tag 071Q;
3. the phrase "`E` is `m`-pseudo-coherent relative to `Y`" is taken to mean "`E₀` is
   `m`-pseudo-coherent relative to `Y₀`" in the sense of More on Morphisms, Section 09UH.

The first is `AlgebraicGeometry.Space.locallyOfFiniteType_of_represents`. This file supplies the
second and the third.

## Main definitions

* `AlgebraicGeometry.Space.representableDerivedPullback`: the pullback
  `D(𝒪_{X₀}) ⥤ D(𝒪_X)` of complexes on the scheme `X₀` to the algebraic space `X` it represents,
  given an identification `h_{X₀} ≅ X`.
* `AlgebraicGeometry.Space.representableDerivedDescent`: the object `E₀` of `D_QCoh(𝒪_{X₀})`
  whose pullback is a given `E` in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.IsRepresentablyRelativelyPseudoCoherentFrom`: the convention of
  assertion 3, `E` is `m`-pseudo-coherent relative to `Y` when `E₀` is `m`-pseudo-coherent
  relative to `Y₀` (Stacks 09UI).

## Main results

* `AlgebraicGeometry.Space.existsUnique_representableDerivedPullback_iso`: assertion 2.
* `AlgebraicGeometry.Space.isRepresentablyRelativelyPseudoCoherentFrom_iff`: the convention of
  assertion 3 does not depend on the choice of `E₀`: it holds exactly when every object of
  `D_QCoh(𝒪_{X₀})` pulling back to `E` is `m`-pseudo-coherent relative to `Y₀`.

## Implementation notes

A representable algebraic space is a presheaf `X` on the big fppf site together with an
isomorphism `eX : h_{X₀} ≅ X` from the presheaf represented by an object `X₀` of the site, and
`f₀` represents `f` when the square formed by `eX`, the analogous `eY`, `f₀` and `f` commutes, as
in `AlgebraicGeometry.Space.locallyOfFiniteType_of_represents`.

The pullback of an object `E₀` of `D(𝒪_{X₀})` to `X` is formed in two steps. First the associated
module functor `ε^*` of Stacks 03DU (4), from the Zariski site of the scheme `X₀` to the small
étale site of the representable algebraic space `h_{X₀}`; on derived categories this is
`AlgebraicGeometry.Space.representedDerivedAssociatedModule`, and on `D_QCoh` it is the
equivalence of Stacks 071Q (`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`)
read on `h_{X₀}`. Then the transport along the isomorphism `X ≅ h_{X₀}` of algebraic spaces,
the étale pullback `AlgebraicGeometry.Space.derivedEtaleModulePullbackEquivalenceOfIso`, an
equivalence of derived categories which preserves quasi-coherence of the cohomology sheaves.

"Unique" is uniqueness up to isomorphism, the only uniqueness an object of a category has: any
two objects of `D_QCoh(𝒪_{X₀})` pulling back to `E` are isomorphic.

## References

* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 09UH](https://stacks.math.columbia.edu/tag/09UH)
* [Stacks Project, Tag 09UI](https://stacks.math.columbia.edu/tag/09UI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

section

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {U : BigFppfOver B S hS} (eX : yoneda.obj U ≅ X)

/-- An identification `h_U ≅ X` of the presheaf represented by an object `U` of the big fppf site
with an algebraic space `X`, as the isomorphism `X ≅ h_U` of algebraic spaces. -/
abbrev representableSpaceIso :
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) ≅ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  ObjectProperty.isoMk _ eX.symm

end

/-! The rest of the file works in `D_QCoh(𝒪_X)`,
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, through the derived associated-module
functor `AlgebraicGeometry.Space.representedDerivedAssociatedModule` of Stacks 071Q and with
relative pseudo-coherence `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` of Stacks 09UI, all
of which are constructed at the standard derived categories. -/

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

section Descent

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {U : BigFppfOver B S hS} (eX : yoneda.obj U ≅ X)

/-- The pullback `E₀ ↦ E₀|_X` of complexes of `𝒪_{X₀}`-modules on the scheme `X₀` underlying `U`
to the algebraic space `X` it represents through `eX : h_U ≅ X`: the associated module functor
`ε^* : D(𝒪_{X₀}) ⥤ D(𝒪_{h_U})` followed by the transport along `X ≅ h_U`. -/
def representableDerivedPullback :
    DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules ⥤
      DerivedCategory (Modules.{u, u} B S hS X hX) :=
  representedDerivedAssociatedModule B S hS U ⋙
    (derivedEtaleModulePullbackEquivalenceOfIso B S hS (representableSpaceIso B S hS hX eX)).functor

/-- Every object `E` of `D_QCoh(𝒪_X)` is the pullback of an object of `D_QCoh(𝒪_{X₀})`. -/
theorem exists_representableDerivedPullback_iso
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    ∃ E₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent) ∧
        Nonempty ((representableDerivedPullback B S hS hX eX).obj E₀ ≅ E.obj) := by
  let Φ := derivedEtaleModulePullbackEquivalenceOfIso B S hS (representableSpaceIso B S hS hX eX)
  obtain ⟨ω, hω, ⟨e⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS U
    (Φ.inverse.obj E.obj) (derivedQuasicoherent_etaleModulePullback B S hS
      (representableSpaceIso B S hS hX eX).inv (isEtale_hom_of_isIso B S hS _) E.obj E.property)
  exact ⟨ω, hω, ⟨Φ.functor.mapIso e ≪≫ Φ.counitIso.app E.obj⟩⟩

/-- Two objects of `D_QCoh(𝒪_{X₀})` with isomorphic pullbacks to `X` are isomorphic. -/
theorem nonempty_iso_of_representableDerivedPullback_iso
    (E₀ E₀' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent)
    (hE₀' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀').IsQuasicoherent)
    (e : (representableDerivedPullback B S hS hX eX).obj E₀ ≅
      (representableDerivedPullback B S hS hX eX).obj E₀') :
    Nonempty (E₀ ≅ E₀') :=
  nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS U E₀ E₀' hE₀ hE₀'
    ((derivedEtaleModulePullbackEquivalenceOfIso B S hS
      (representableSpaceIso B S hS hX eX)).fullyFaithfulFunctor.preimageIso e)

/-- Let `X` be an algebraic space represented by the scheme `X₀` underlying `U`, through
`eX : h_U ≅ X`. Every object `E` of `D_QCoh(𝒪_X)` is the pullback of an object `E₀` of
`D(𝒪_{X₀})` with quasi-coherent cohomology sheaves, and `E₀` is unique: any object of
`D_QCoh(𝒪_{X₀})` whose pullback is isomorphic to `E` is isomorphic to `E₀`. -/
@[stacks 0CSW "every E in D_QCoh(O_X) is the pullback of a unique E_0 in D_QCoh(O_{X_0}), \
by Tag 071Q"]
theorem existsUnique_representableDerivedPullback_iso
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    ∃ E₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent) ∧
        Nonempty ((representableDerivedPullback B S hS hX eX).obj E₀ ≅ E.obj) ∧
          ∀ E₀' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules,
            (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀').IsQuasicoherent) →
              Nonempty ((representableDerivedPullback B S hS hX eX).obj E₀' ≅ E.obj) →
                Nonempty (E₀' ≅ E₀) := by
  obtain ⟨E₀, hE₀, ⟨e⟩⟩ := exists_representableDerivedPullback_iso B S hS hX eX E
  exact ⟨E₀, hE₀, ⟨e⟩, fun E₀' hE₀' ⟨e'⟩ =>
    nonempty_iso_of_representableDerivedPullback_iso B S hS hX eX E₀' E₀ hE₀' hE₀ (e' ≪≫ e.symm)⟩

/-- The object `E₀` of `D_QCoh(𝒪_{X₀})` whose pullback to `X` is `E`, for an algebraic space `X`
represented by the scheme `X₀` underlying `U` through `eX : h_U ≅ X`. It is unique up to
isomorphism by `AlgebraicGeometry.Space.existsUnique_representableDerivedPullback_iso`. -/
def representableDerivedDescent (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (exists_representableDerivedPullback_iso B S hS hX eX E).choose

/-- The cohomology sheaves of `E₀` are quasi-coherent. -/
theorem isQuasicoherent_homology_representableDerivedDescent
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).obj
      (representableDerivedDescent B S hS hX eX E)).IsQuasicoherent :=
  (exists_representableDerivedPullback_iso B S hS hX eX E).choose_spec.1 i

/-- The pullback of `E₀` to `X` is `E`. -/
def representableDerivedPullbackDescentIso (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    (representableDerivedPullback B S hS hX eX).obj (representableDerivedDescent B S hS hX eX E) ≅
      E.obj :=
  (exists_representableDerivedPullback_iso B S hS hX eX E).choose_spec.2.some

/-- Any object of `D_QCoh(𝒪_{X₀})` whose pullback to `X` is isomorphic to `E` is isomorphic to
`E₀`. -/
theorem nonempty_iso_representableDerivedDescent
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (E₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent)
    (e : (representableDerivedPullback B S hS hX eX).obj E₀ ≅ E.obj) :
    Nonempty (E₀ ≅ representableDerivedDescent B S hS hX eX E) :=
  nonempty_iso_of_representableDerivedPullback_iso B S hS hX eX E₀ _ hE₀
    (isQuasicoherent_homology_representableDerivedDescent B S hS hX eX E)
    (e ≪≫ (representableDerivedPullbackDescentIso B S hS hX eX E).symm)

end Descent

section RelativePseudoCoherence

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) {U V : BigFppfOver B S hS} (f₀ : U ⟶ V)
  (eX : yoneda.obj U ≅ X) (eY : yoneda.obj V ≅ Y) (hrep : yoneda.map f₀ ≫ eY.hom = eX.hom ≫ f)

/-- Let `f : X → Y` be a morphism of representable algebraic spaces over `S` which is locally of
finite type, represented by the morphism of schemes `f₀ : X₀ → Y₀` underlying `f₀ : U ⟶ V`
through `eX : h_U ≅ X` and `eY : h_V ≅ Y`. An object `E` of `D_QCoh(𝒪_X)` is
*`m`-pseudo-coherent relative to `Y`* when the object `E₀` of `D_QCoh(𝒪_{X₀})` whose pullback is
`E` is `m`-pseudo-coherent relative to `Y₀` in the sense of Stacks 09UI. This makes sense because
`f₀` is locally of finite type (`AlgebraicGeometry.Space.locallyOfFiniteType_of_represents`), and
it does not depend on the choice of `E₀`
(`AlgebraicGeometry.Space.isRepresentablyRelativelyPseudoCoherentFrom_iff`). -/
@[stacks 0CSW "the convention: E is m-pseudo-coherent relative to Y when E_0 is \
m-pseudo-coherent relative to Y_0 (Tag 09UI)"]
def IsRepresentablyRelativelyPseudoCoherentFrom
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ) : Prop :=
  haveI := locallyOfFiniteType_of_represents B S hS f hf U V f₀ eX eY hrep
  Scheme.Hom.IsPseudoCoherentFrom ((BigFppfOver.toScheme B S hS).map f₀)
    (representableDerivedDescent B S hS hX eX E) m

/-- **The convention of Stacks 0CSW does not depend on the choice of `E₀`.** `E` is
`m`-pseudo-coherent relative to `Y` exactly when every object of `D_QCoh(𝒪_{X₀})` whose pullback
to `X` is isomorphic to `E` is `m`-pseudo-coherent relative to `Y₀`. -/
theorem isRepresentablyRelativelyPseudoCoherentFrom_iff
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ) :
    IsRepresentablyRelativelyPseudoCoherentFrom B S hS hX f hf f₀ eX eY hrep E m ↔
      ∀ E₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent) →
          Nonempty ((representableDerivedPullback B S hS hX eX).obj E₀ ≅ E.obj) →
            haveI := locallyOfFiniteType_of_represents B S hS f hf U V f₀ eX eY hrep
            Scheme.Hom.IsPseudoCoherentFrom ((BigFppfOver.toScheme B S hS).map f₀) E₀ m := by
  have := locallyOfFiniteType_of_represents B S hS f hf U V f₀ eX eY hrep
  refine ⟨fun h E₀ hE₀ ⟨e⟩ => ?_, fun h => h _
    (isQuasicoherent_homology_representableDerivedDescent B S hS hX eX E)
    ⟨representableDerivedPullbackDescentIso B S hS hX eX E⟩⟩
  obtain ⟨e₀⟩ := nonempty_iso_representableDerivedDescent B S hS hX eX E E₀ hE₀ e
  exact Scheme.Hom.IsPseudoCoherentFrom.of_iso _ h e₀.symm

end RelativePseudoCoherence

end StandardModel

end AlgebraicGeometry.Space

end
