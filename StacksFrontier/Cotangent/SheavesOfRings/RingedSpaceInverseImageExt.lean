module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.RingedSpace.FlatOfIsoStalkMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback

/-!
# `Ext` out of a derived pullback, read on the inverse-image ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  It factors as

`(X, 𝒪_X) --ι--> (X, f⁻¹𝒪_Y) --π--> (Y, 𝒪_Y)`,

where `(X, f⁻¹𝒪_Y)` is the inverse-image ringed space, `π` is its canonical projection and `ι` is
the identity on spaces with structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.  The projection `π` is flat, so
`Lπ^*` is the degreewise pullback `π^*`, and `ι_*` is restriction of scalars along `f♯`, which
is exact.  Hence for `K` in `D(𝒪_Y)` and an `𝒪_X`-module `𝒢`

`Ext^n_{𝒪_X}(Lf^*K, 𝒢) = Ext^n_{f⁻¹𝒪_Y}(π^*K, ι_*𝒢)`,

by `Lf^* = Lι^* ∘ Lπ^*` and the adjunction `Lι^* ⊣ Rι_*`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.inverseImageSourceInclusion`: the morphism `ι`.
* `AlgebraicGeometry.RingedSpace.derivedPullbackExtEquivOfIso`: the identification of the two
  `Ext^n` groups, for any object `P ≅ π^*K` of `D(f⁻¹𝒪_Y)`.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageSourceInclusion_comp_projection`: `ι ≫ π = f`.
* `AlgebraicGeometry.RingedSpace.derivedPullbackExtEquivOfIso_naturality`: the identification is
  natural in the coefficient module `𝒢`.

## Implementation notes

The model of the derived categories is `HasDerivedCategory.standard` as a local instance, the
model the derived pullback and its adjunction (Tags 06YJ and 079W) are stated for here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The morphism `ι : (X, 𝒪_X) ⟶ (X, f⁻¹𝒪_Y)`: the identity on spaces, with structure map the
transpose `f⁻¹𝒪_Y ⟶ 𝒪_X` of `f♯`. -/
def inverseImageSourceInclusion : X ⟶ inverseImage Y f.hom.base :=
  Stacks.Cohomology.SupportedComplexes.inverseImageRingedSpaceLift Y f.hom.base
    (𝟙 X.carrier) ⟨f.hom.c⟩

/-- `ι` lies over the identity of `X`. -/
@[simp]
theorem inverseImageSourceInclusion_base :
    (inverseImageSourceInclusion f).hom.base = 𝟙 X.carrier :=
  rfl

/-- **`f = π ∘ ι`**: a morphism of ringed spaces factors through the inverse-image ringed space
of its continuous map. -/
theorem inverseImageSourceInclusion_comp_projection :
    inverseImageSourceInclusion f ≫ inverseImageProjection Y f.hom.base = f := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ rfl ?_
  exact heq_of_eq (Stacks.Cohomology.SupportedComplexes.inverseImageRingedSpaceLift_comp_c Y
    f.hom.base (Y := X) (𝟙 X.carrier) ⟨f.hom.c⟩)

/-- Pushforward along `ι` is exact: `ι` is a homeomorphism on spaces. -/
instance : IsIso (inverseImageSourceInclusion f).hom.base := by
  rw [inverseImageSourceInclusion_base]
  exact IsIso.id X.carrier

/-- Pullback along the flat projection `(X, f⁻¹𝒪_Y) ⟶ (Y, 𝒪_Y)` is left exact. -/
instance preservesFiniteLimits_modulePullback_inverseImageProjection {Z : TopCat.{u}}
    (i : Z ⟶ Y.carrier) : PreservesFiniteLimits (modulePullback (inverseImageProjection Y i)) :=
  preservesFiniteLimits_modulePullback_of_isFlat _ (isFlat_inverseImageProjection Y i)

/-- Pullback along the projection `(X, f⁻¹𝒪_Y) ⟶ (Y, 𝒪_Y)` is right exact, being a left
adjoint. -/
instance preservesFiniteColimits_modulePullback_inverseImageProjection {Z : TopCat.{u}}
    (i : Z ⟶ Y.carrier) : PreservesFiniteColimits (modulePullback (inverseImageProjection Y i)) :=
  letI : PreservesColimitsOfSize.{u, u} (modulePullback (inverseImageProjection Y i)) :=
    (modulePullbackPushforwardAdjunction (inverseImageProjection Y i)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Derived pullback along equal morphisms. -/
def derivedPullbackObjIsoOfEq {g g' : X ⟶ Y} (h : g = g')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback g).obj K ≅ (derivedPullback g').obj K := by
  subst h
  exact Iso.refl _

/-- `Lf^*K ≅ Lι^*(π^*K)`: the derived pullback along `f`, read through the factorization
`f = π ∘ ι`, with `Lπ^* = π^*` because `π` is flat. -/
def derivedPullbackIsoInverseImage
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback f).obj K ≅
      (derivedPullback (inverseImageSourceInclusion f)).obj
        ((modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj K) :=
  (derivedPullbackObjIsoOfEq (inverseImageSourceInclusion_comp_projection f) K).symm ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (inverseImageSourceInclusion f) (inverseImageProjection Y f.hom.base)).app K).symm ≪≫
    (derivedPullback (inverseImageSourceInclusion f)).mapIso
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory
        (inverseImageProjection Y f.hom.base)
        (isFlat_inverseImageProjection Y f.hom.base)).app K)

/-- `(ι_*𝒢)[0]⟦n⟧ ≅ Rι_*(𝒢[0]⟦n⟧)`, naturally in the `𝒪_X`-module `𝒢`: pushforward along `ι`
is exact, so it is computed degreewise and commutes with shifts and with placing a module in
degree `0`. -/
def singleShiftDerivedPushforwardNatIso (n : ℤ) :
    modulePushforward (inverseImageSourceInclusion f) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ n ≅
      DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
        derivedPushforward (inverseImageSourceInclusion f) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((modulePushforward (inverseImageSourceInclusion f)).mapDerivedCategorySingleFunctor 0).symm
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (((modulePushforward (inverseImageSourceInclusion f)).mapDerivedCategory.commShiftIso
          n).symm ≪≫
        Functor.isoWhiskerLeft _ (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
          (modulePushforward (inverseImageSourceInclusion f))))

/-- Precomposition with an isomorphism, as an additive equivalence of hom groups. -/
def precompIsoAddEquiv {C : Type*} [Category C] [Preadditive C] {A B : C} (e : A ≅ B) (Z : C) :
    (B ⟶ Z) ≃+ (A ⟶ Z) where
  toFun φ := e.hom ≫ φ
  invFun ψ := e.inv ≫ ψ
  left_inv φ := by simp
  right_inv ψ := by simp
  map_add' φ ψ := Preadditive.comp_add _ _ _ _ _ _

/-- **`Hom_{D(f⁻¹𝒪_Y)}(P, (ι_*𝒢)[n]) = Ext^n_{𝒪_X}(Lf^*K, 𝒢)`** for an object `P` of
`D(f⁻¹𝒪_Y)` identified with `π^*K`.  The derived pullback along `f` is `Lι^* ∘ π^*`, and `Lι^*` is
left adjoint to `Rι_* = ι_*`, restriction of scalars along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.  For `P = π^*K`
itself take `eP = Iso.refl _`. -/
def derivedPullbackExtEquivOfIso
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {P : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base)))}
    (eP : (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj K ≅ P)
    (G : SheafOfModules.{u} (structureSheafRing X)) (n : ℤ) :
    (P ⟶ ((DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) ≃+
      ((derivedPullback f).obj K ⟶ ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  haveI := (derivedAdjunction (inverseImageSourceInclusion f)).right_adjoint_additive
  (Stacks.Injectives.homCongrAddEquiv eP.symm
      ((singleShiftDerivedPushforwardNatIso f n).app G)).trans
    (((derivedAdjunction (inverseImageSourceInclusion f)).homAddEquiv _ _).symm.trans
      (precompIsoAddEquiv (derivedPullbackIsoInverseImage f K) _))

/-- The identification of `derivedPullbackExtEquivOfIso`, written out: precompose with `eP`,
postcompose with the comparison `(ι_*𝒢)[0]⟦n⟧ ≅ Rι_*(𝒢[0]⟦n⟧)`, transpose along `Lι^* ⊣ Rι_*`,
and precompose with `Lf^*K ≅ Lι^*(π^*K)`. -/
theorem derivedPullbackExtEquivOfIso_apply
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {P : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base)))}
    (eP : (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj K ≅ P)
    (G : SheafOfModules.{u} (structureSheafRing X)) (n : ℤ)
    (a : P ⟶ ((DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) :
    derivedPullbackExtEquivOfIso f K eP G n a =
      (derivedPullbackIsoInverseImage f K).hom ≫
        ((derivedAdjunction (inverseImageSourceInclusion f)).homEquiv _ _).symm
          (eP.hom ≫ a ≫ (singleShiftDerivedPushforwardNatIso f n).hom.app G) :=
  rfl

/-- **Naturality in the coefficient module.**  For `g : 𝒢 ⟶ 𝒢'` the identification of
`derivedPullbackExtEquivOfIso` carries postcomposition with `(ι_*g)[0]⟦n⟧` to postcomposition with
`g[0]⟦n⟧`. -/
theorem derivedPullbackExtEquivOfIso_naturality
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {P : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base)))}
    (eP : (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj K ≅ P)
    {G G' : SheafOfModules.{u} (structureSheafRing X)} (g : G ⟶ G') (n : ℤ)
    (a : P ⟶ ((DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) :
    derivedPullbackExtEquivOfIso f K eP G' n
        (a ≫ ((DerivedCategory.singleFunctor _ 0).map
          ((modulePushforward (inverseImageSourceInclusion f)).map g))⟦n⟧') =
      derivedPullbackExtEquivOfIso f K eP G n a ≫
        ((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧' := by
  refine (derivedPullbackExtEquivOfIso_apply f K eP G' n _).trans (Eq.trans ?_
    (congrArg (· ≫ ((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧')
      (derivedPullbackExtEquivOfIso_apply f K eP G n a)).symm)
  have hnat : ((DerivedCategory.singleFunctor _ 0).map
        ((modulePushforward (inverseImageSourceInclusion f)).map g))⟦n⟧' ≫
        (singleShiftDerivedPushforwardNatIso f n).hom.app G' =
      (singleShiftDerivedPushforwardNatIso f n).hom.app G ≫
        (derivedPushforward (inverseImageSourceInclusion f)).map
          (((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧') :=
    (singleShiftDerivedPushforwardNatIso f n).hom.naturality g
  have h3 : eP.hom ≫ (a ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((modulePushforward (inverseImageSourceInclusion f)).map g))⟦n⟧') ≫
        (singleShiftDerivedPushforwardNatIso f n).hom.app G' =
      (eP.hom ≫ a ≫ (singleShiftDerivedPushforwardNatIso f n).hom.app G) ≫
        (derivedPushforward (inverseImageSourceInclusion f)).map
          (((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧') := by
    simp only [Category.assoc, hnat]
  have h2 := (derivedAdjunction (inverseImageSourceInclusion f)).homEquiv_naturality_right_symm
    (eP.hom ≫ a ≫ (singleShiftDerivedPushforwardNatIso f n).hom.app G)
    (((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧')
  exact (congrArg (fun x => (derivedPullbackIsoInverseImage f K).hom ≫
      ((derivedAdjunction (inverseImageSourceInclusion f)).homEquiv _ _).symm x) h3).trans
    ((congrArg ((derivedPullbackIsoInverseImage f K).hom ≫ ·) h2).trans
      (Category.assoc _ _ _).symm)

end AlgebraicGeometry.RingedSpace

end
