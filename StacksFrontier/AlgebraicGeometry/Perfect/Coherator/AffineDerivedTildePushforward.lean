module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.DerivedAdjunctionOfExactLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Derived pushforward between affine schemes

For a ring map `φ : R ⟶ S`, derived direct image along `Spec φ` agrees naturally with
restriction of scalars under the affine associated-sheaf functors. Both routes take values in
complexes with quasi-coherent cohomology.

The associated-sheaf functor `M ↦ M^~` is exact, so it induces a functor of derived categories
whose cohomology sheaves are the associated sheaves of the cohomology modules, hence
quasi-coherent. Derived direct image along `Spec φ`, an affine morphism, preserves
quasi-coherent cohomology by [Stacks, Tag 08D7]. The square then commutes because, after
composing with the inclusion into the ambient derived category, it is the derived form of
[Stacks, Tag 01I9] combined with the comparison square of [Stacks, Tag 08D7].

## Main definitions

* `AlgebraicGeometry.affineTildeQuasicoherent` is derived affine sheafification with its
  quasi-coherent codomain.
* `AlgebraicGeometry.affineDerivedPushforwardQuasicoherent` is derived direct image between the
  quasi-coherent derived categories of the two affine schemes.
* `AlgebraicGeometry.affineDerivedPushforwardIso` is the natural isomorphism of the two routes.

## Main results

* `AlgebraicGeometry.affineTilde_isQuasicoherent`: associated derived sheaves have
  quasi-coherent cohomology.
* `AlgebraicGeometry.affineDerivedPushforward_isQuasicoherent`: derived direct image preserves
  quasi-coherent cohomology for this affine map.

## Implementation notes

The square is expressed by a natural isomorphism rather than a literal equality of functors.
The full-subcategory inclusions recover the ordinary exact derived associated-sheaf functors
and the chosen right derived pushforward, so the identification takes place in the
quasi-coherent derived categories and not only in the ambient derived categories of all sheaves
of modules.

## References

* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedAdjunction (homotopyUnitOfComplex homotopyUnitOfComplex_isRightDerivedFunctor)

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

public theorem affineTilde_isQuasicoherent (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      ((tilde.functor R).mapDerivedCategory.obj M) := fun n =>
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (tilde.functor R) n).app M).symm
    (inferInstanceAs ((tilde.functor R).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)).IsQuasicoherent)

/-- Derived affine sheafification, regarded as taking values in the quasi-coherent derived
category. -/
public noncomputable def affineTildeQuasicoherent (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ⥤ QuasicoherentDerivedCategory (Spec R) :=
  ObjectProperty.lift _ (tilde.functor R).mapDerivedCategory
    (affineTilde_isQuasicoherent R)

/-- **Stacks Project, Tag 0DJK.** Derived direct image under a morphism of affine schemes
preserves quasi-coherent cohomology. -/
@[stacks 0DJK "pushforward route"]
public theorem affineDerivedPushforward_isQuasicoherent
    (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (Rf : DerivedCategory (Spec S).Modules ⥤ DerivedCategory (Spec R).Modules)
    (α : (Scheme.Modules.pushforward (Spec.map φ)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (Spec S).Modules (.up ℤ))]
    (K : QuasicoherentDerivedCategory (Spec S)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (Rf.obj K.obj) :=
  have : Rf.IsRightDerivedFunctor
      (homotopyUnitOfComplex (Scheme.Modules.pushforward (Spec.map φ)) Rf α)
      (HomotopyCategory.quasiIso (Spec S).Modules (.up ℤ)) :=
    homotopyUnitOfComplex_isRightDerivedFunctor
      (Scheme.Modules.pushforward (Spec.map φ)) Rf α
  affineRightDerivedPushforward_mem (Spec.map φ) Rf
    (homotopyUnitOfComplex (Scheme.Modules.pushforward (Spec.map φ)) Rf α) K

/-- Derived pushforward between the quasi-coherent derived categories of affine schemes. -/
public noncomputable def affineDerivedPushforwardQuasicoherent
    (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (Rf : DerivedCategory (Spec S).Modules ⥤ DerivedCategory (Spec R).Modules)
    (α : (Scheme.Modules.pushforward (Spec.map φ)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (Spec S).Modules (.up ℤ))] :
    QuasicoherentDerivedCategory (Spec S) ⥤ QuasicoherentDerivedCategory (Spec R) :=
  ObjectProperty.lift _ ((ObjectProperty.ι _) ⋙ Rf)
    (fun K => affineDerivedPushforward_isQuasicoherent R S φ Rf α K)

/-- **Stacks Project, Tag 0DJK.** The affine associated-sheaf/derived-pushforward square
commutes naturally: derived direct image corresponds to restriction of scalars. -/
@[stacks 0DJK "commutativity"]
public noncomputable def affineDerivedPushforwardIso
    (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (Rf : DerivedCategory (Spec S).Modules ⥤ DerivedCategory (Spec R).Modules)
    (α : (Scheme.Modules.pushforward (Spec.map φ)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (Spec S).Modules (.up ℤ))] :
    affineTildeQuasicoherent S ⋙ affineDerivedPushforwardQuasicoherent R S φ Rf α ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙ affineTildeQuasicoherent R := by
  let F := Scheme.Modules.pushforward (Spec.map φ)
  let β := homotopyUnitOfComplex F Rf α
  let : Rf.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (Spec S).Modules (.up ℤ)) :=
    homotopyUnitOfComplex_isRightDerivedFunctor F Rf α
  let T := (tildeEquiv (R := S)).functor
  let U := (tildeEquiv (R := R)).functor
  let I : Scheme.QuasicoherentModules (Spec S) ⥤ (Spec S).Modules :=
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι
  let J : Scheme.QuasicoherentModules (Spec R) ⥤ (Spec R).Modules :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι
  let : I.Additive := Functor.fullSubcategoryInclusion_additive _
  let : J.Additive := Functor.fullSubcategoryInclusion_additive _
  let : J.Full := (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι.full
  let : J.Faithful :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι.faithful
  let : PreservesFiniteLimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits (Spec S)
  let : PreservesFiniteColimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits
      (Spec S)
  let : PreservesFiniteLimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits (Spec R)
  let : PreservesFiniteColimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits
      (Spec R)
  let V := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι
  let : V.Full := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι.full
  let : V.Faithful := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι.faithful
  let P := quasicoherentPushforward (Spec.map φ)
  let B := ModuleCat.restrictScalars φ.hom
  let : T.Additive := T.additive_of_preserves_binary_products
  let : U.Additive := U.additive_of_preserves_binary_products
  let e : T ⋙ P ≅ B ⋙ U :=
    ((Functor.whiskeringRight _ _ _).obj J).preimageIso
      (show (T ⋙ P) ⋙ J ≅ (B ⋙ U) ⋙ J from pushforwardTildeIso R S φ)
  let eD : T.mapDerivedCategory ⋙ P.mapDerivedCategory ≅
      B.mapDerivedCategory ⋙ U.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIsoOfCompIso e ≪≫
      (Functor.mapDerivedCategoryCompIsoOfCompIso (F := B) (G := U) (H := B ⋙ U) (Iso.refl _)).symm
  let eS := Functor.mapDerivedCategoryCompIsoOfCompIso (F := T) (G := I) (H := tilde.functor S)
    (Iso.refl _)
  let eR := Functor.mapDerivedCategoryCompIsoOfCompIso (F := U) (G := J) (H := tilde.functor R)
    (Iso.refl _)
  let eP := (affineDerivedPushforward_comparison (Spec.map φ) Rf β).exists.choose
  let eI : I.mapDerivedCategory ⋙ Rf ≅ P.mapDerivedCategory ⋙ J.mapDerivedCategory :=
    Functor.isoWhiskerRight
      (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι
        (Spec S)).symm Rf ≪≫
      (show (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison
          (Spec S) ⋙ (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).ι) ⋙ Rf ≅
        (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison (Spec S) ⋙
          affineRightDerivedPushforward (Spec.map φ) Rf β) ⋙ V from Iso.refl _) ≪≫
      Functor.isoWhiskerRight eP V ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.mapDerivedCategory
        (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι
          (Spec R))
  refine ((Functor.whiskeringRight _ _ _).obj V).preimageIso ?_
  change (tilde.functor S).mapDerivedCategory ⋙ Rf ≅
    B.mapDerivedCategory ⋙ (tilde.functor R).mapDerivedCategory
  exact Functor.isoWhiskerRight eS.symm Rf ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft T.mapDerivedCategory eI ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eD J.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft B.mapDerivedCategory eR

end AlgebraicGeometry

end
