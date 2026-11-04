module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDirectImageAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.Homology.CompositeCollapseBottomRow

/-!
# Higher direct images along a morphism of represented algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
`φ` is quasi-compact and separated, and let `𝓕` be a quasi-coherent `𝒪_{T'}`-module. Write `h_g`
for the morphism of algebraic spaces `yoneda.map g` and `𝓕^a` for the module on the small étale
site of `h_{T'}` associated with `𝓕`. This file proves

`R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a`

for every `k`: Stacks 071N, read in the spaces formalism, for a separated morphism.

## The proof

Let `ε_* : Mod(𝒪_{h_T}) ⥤ Mod(𝒪_T)` be the direct image to the Zariski site
(`AlgebraicGeometry.Space.representedZariskiDirectImageSchemeModules`); it is right adjoint to
`(-)^a`, which is exact, so it preserves injectives. The two composites round the square

```
Mod(h_{T'}) --(h_g)_*--> Mod(h_T)
    | ε'_*                  | ε_*
Mod(T')     ----φ_*---->  Mod(T)
```

agree (`AlgebraicGeometry.Space.representedZariskiDirectImagePushforwardIso`). Their right derived
functors at `𝓕^a` are computed twice:

* along the bottom-left route, `𝓕^a` is `ε'_*`-acyclic (it is quasi-coherent) and `ε'_*` keeps
  injectives, so `R ᵏ (φ_* ∘ ε'_*)(𝓕^a) = R ᵏ φ_* (ε'_* 𝓕^a) = R ᵏ φ_* 𝓕`
  (`Stacks.RightDerivedComp.objIso`);
* along the top-right route, the direct image of an injective is `ε_*`-acyclic (Stacks 072Z) and
  so is every `R ᵠ (h_g)_* (𝓕^a)`, which is quasi-coherent by the separated case of Stacks 0720;
  so `R ᵏ (ε_* ∘ (h_g)_*)(𝓕^a) = ε_* R ᵏ (h_g)_* (𝓕^a)`
  (`Stacks.RightDerivedComp.objIsoOfAcyclicHigherImages`).

Hence `ε_* R ᵏ (h_g)_* (𝓕^a) ≅ R ᵏ φ_* 𝓕`, and a quasi-coherent module on `h_T` is the associated
module of its direct image to the Zariski site (Stacks 03DX).

## Main results

* `AlgebraicGeometry.Space.nonempty_rightDerived_modulePushforward_representedSpaceMap_iso`:
  `R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a` for `φ` quasi-compact and separated.

## Implementation notes

**No `@[stacks 071N]` attribute.** The source's statement is for a quasi-compact and
quasi-separated `φ`; the quasi-coherence of `R ᵠ (h_g)_* (𝓕^a)` used above is proved in this
development only for a separated morphism (Stacks 0720 in that case), so this is the separated
case of the tag.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `(-)^a ⊣ ε_*` for a represented algebraic space: the associated module of Stacks 03DU (4),
transported to the small étale site of `h_U`, is left adjoint to the direct image to the Zariski
site of the scheme underlying `U`. -/
def representedAssociatedModuleZariskiAdjunction (U : BigFppfOver B S hS) :
    representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⊣
      representedZariskiDirectImageSchemeModules B S hS U :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedModuleEquivalence.{u, u} B S hS U).toAdjunction

/-- `ε_*` preserves injective objects, its left adjoint `(-)^a` being exact. -/
theorem injective_representedZariskiDirectImage_obj (U : BigFppfOver B S hS)
    (I : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    [Injective I] : Injective ((representedZariskiDirectImageSchemeModules B S hS U).obj I) :=
  (representedAssociatedModuleZariskiAdjunction B S hS U).map_injective I inferInstance

/-- `ε_*` of the associated module of a quasi-coherent module is the module itself
(Stacks 0GN7). -/
def representedZariskiDirectImageAssociatedModuleIso (U : BigFppfOver B S hS)
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hF : F.IsQuasicoherent) :
    (representedZariskiDirectImageSchemeModules B S hS U).obj
        ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj F) ≅ F :=
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨F, hF⟩
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      ((representedModuleEquivalence.{u, u} B S hS U).unitIso.app _).symm ≪≫
    (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).unit.app
        F)).symm

/-- A quasi-coherent module on a represented algebraic space is the associated module of a
quasi-coherent module on the scheme (Stacks 03DX). -/
theorem exists_isQuasicoherent_iso_representedAssociatedModule_of_isQuasicoherentOnSite
    (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    ∃ G : ((BigFppfOver.toScheme B S hS).obj U).Modules, G.IsQuasicoherent ∧
      Nonempty ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G ≅
        M) := by
  let Q := representedQuasicoherentSchemeEquivalence B S hS U
  let X : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)).FullSubcategory := ⟨M, hM⟩
  exact ⟨(Q.inverse.obj X).obj, (Q.inverse.obj X).property,
    ⟨(ObjectProperty.ι _).mapIso (Q.counitIso.app X)⟩⟩

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The two module equivalences between the small étale sites of `T` and of `h_T` have
isomorphic inverses: their functors are both the direct image along the identification of the
sites. -/
def representedSmallEtaleModuleEquivalenceInverseIso (U : BigFppfOver B S hS) :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse ≅
      representedModuleRestriction B S hS U :=
  Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS U).inverse
      (representedModuleEquivalence.{u, u} B S hS U).unitIso ≪≫
    Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalence B S hS U).counitIso
      (representedModuleRestriction B S hS U) ≪≫ Functor.leftUnitor _

/-- **The square of direct images.** Taking the direct image along `h_g` and then restricting to
the Zariski site of `T` is restricting to the Zariski site of `T'` and then taking the direct image
along the morphism of schemes underlying `g`. -/
def representedZariskiDirectImagePushforwardIso :
    modulePushforward B S hS (representedSpaceMap B S hS g) ⋙
        representedZariskiDirectImageSchemeModules B S hS T ≅
      representedZariskiDirectImageSchemeModules B S hS T' ⋙
        Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g) :=
  let eT' := representedSmallEtaleModuleEquivalence B S hS T'
  let sq := representedModulePushforwardSquareIso B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)
  Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight eT'.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eT'.inverse sq.symm)
      (representedZariskiDirectImageSchemeModules B S hS T) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eT'.inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.pushforward.{u}
          (representedSchemeStructureMapRing B S hS g))
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              ((representedModuleEquivalence.{u, u} B S hS T).unitIso.symm)
              (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property) ≪≫
            Functor.leftUnitor _) ≪≫
        _root_.AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso
          (associatedBigEtaleSite B) g.left) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalenceInverseIso B S hS T') _) _

/-- `ε_*` preserves finite limits, being a right adjoint. -/
private theorem preservesFiniteLimits_representedZariskiDirectImage (U : BigFppfOver B S hS) :
    PreservesFiniteLimits (representedZariskiDirectImageSchemeModules B S hS U) := by
  have :=
    (representedAssociatedModuleZariskiAdjunction B S hS U).rightAdjoint_preservesLimits.{0, 0}
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- **Stacks 071N for a separated morphism, in the spaces formalism.** Let `g : T' ⟶ T` be a
morphism of the big fppf site over `S` whose underlying morphism of schemes `φ` is quasi-compact
and separated, and let `𝓕` be a quasi-coherent `𝒪_{T'}`-module. Then for every `k`

`R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a`,

where `h_g = yoneda.map g` and `(-)^a` is the associated module on the small étale site of the
represented algebraic space. -/
theorem nonempty_rightDerived_modulePushforward_representedSpaceMap_iso
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g))
    (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (hF : F.IsQuasicoherent) (k : ℕ) :
    have :=
      hasInjectiveResolutions_modules B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')
    have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
    Nonempty (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived k).obj
        ((representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived k).obj
          F)) := by
  intro _ _
  have : (modulePushforward B S hS (representedSpaceMap B S hS g) ⋙
      representedZariskiDirectImageSchemeModules B S hS T).Additive := Functor.instAdditiveComp _ _
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have := enoughInjectives_modules B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')
  have := enoughInjectives_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  let P := modulePushforward B S hS (representedSpaceMap B S hS g)
  let P₀ := Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)
  let E := representedZariskiDirectImageSchemeModules B S hS T
  let E' := representedZariskiDirectImageSchemeModules B S hS T'
  let A := (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).obj F
  have hA : A.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_representedAssociatedModule B S hS T' _ F hF
  have : PreservesFiniteLimits E := preservesFiniteLimits_representedZariskiDirectImage B S hS T
  have : PreservesFiniteLimits E' := preservesFiniteLimits_representedZariskiDirectImage B S hS T'
  have hP : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom :=
    isQuasiCompact_yoneda_map B S hS g hqc
  have hPs : IsSeparated B S hS (representedSpaceMap B S hS g).hom :=
    (isSeparated_yoneda_map_iff B S hS g).2 hsep
  have hqcoh : ∀ q, ((P.rightDerived q).obj A).IsQuasicoherentOnSite := fun q ↦
    isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated B S hS _ hP hPs A hA q
  let e₁ : ((P ⋙ E).rightDerived k).obj A ≅ E.obj ((P.rightDerived k).obj A) :=
    Stacks.RightDerivedComp.objIsoOfAcyclicHigherImages P E A
      (fun Z hZ n hn ↦ isZero_rightDerived_representedZariskiDirectImage_modulePushforward B S hS T
        (representedSpaceMap B S hS g) Z hZ n hn)
      (fun q n hn ↦ isZero_rightDerived_representedZariskiDirectImage_of_isQuasicoherentOnSite
        B S hS T _ (hqcoh q) n hn) k
  have : E'.PreservesInjectiveObjects :=
    ⟨fun {I} _ ↦ injective_representedZariskiDirectImage_obj B S hS T' I⟩
  let e₂ : ((E' ⋙ P₀).rightDerived k).obj A ≅ (P₀.rightDerived k).obj (E'.obj A) :=
    Stacks.RightDerivedComp.objIso E' (injectiveResolution A)
      (fun n hn ↦ isZero_rightDerived_representedZariskiDirectImage_of_isQuasicoherentOnSite
        B S hS T' A hA n hn) P₀ k
  let e₃ : ((P ⋙ E).rightDerived k).obj A ≅ ((E' ⋙ P₀).rightDerived k).obj A :=
    (Functor.rightDerivedIsoOfNatIso (representedZariskiDirectImagePushforwardIso B S hS g) k).app A
  let e : E.obj ((P.rightDerived k).obj A) ≅ (P₀.rightDerived k).obj F :=
    e₁.symm ≪≫ e₃ ≪≫ e₂ ≪≫ (P₀.rightDerived k).mapIso
      (representedZariskiDirectImageAssociatedModuleIso B S hS T' F hF)
  obtain ⟨G, hG, ⟨eG⟩⟩ :=
    exists_isQuasicoherent_iso_representedAssociatedModule_of_isQuasicoherentOnSite B S hS T
      ((P.rightDerived k).obj A) (hqcoh k)
  exact ⟨eG.symm ≪≫ (representedAssociatedModule B S hS T _).mapIso
    ((representedZariskiDirectImageAssociatedModuleIso B S hS T G hG).symm ≪≫ E.mapIso eG ≪≫ e)⟩

end AlgebraicGeometry.Space

end
