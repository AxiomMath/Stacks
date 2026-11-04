module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectFullyFaithfulHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback

/-!
# The affine leaf of Stacks 0DKV: the inputs from Stacks 071Q

Let `D` be Situation 0DKU with `X₀` an affine algebraic space, `e₀ : yoneda Z' ≅ X₀`, and let
`R₀` represent the base changes along `e₀ ≫ p₀`.
`AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_of_zariskiModelHomDescent` deduces
the conclusion of Stacks 0DKV for `(K, L)` from the Zariski form
`AlgebraicGeometry.Space.RelativeDescentSituation.ZariskiModelHomDescent` for a pair `(K'', L'')`
of objects of `D(𝒪_{Z'})`, given

1. identifications `ε^*K'' ≅ L(e₀)^*K` and `ε^*L'' ≅ L(e₀)^*L`, and
2. bijectivity of `ε^*` on `Hom(Lq^*K'', Lq^*L'')` at the stages and at the limit of the model.

This file supplies both from Stacks 071Q when `K` and `L` lie in `D_QCoh`.  The first is the
essential surjectivity of `ε^* : D_QCoh(𝒪_{Z'}) ⥤ D_QCoh(𝒪_{h_{Z'}})`, the derived pullback
`L(e₀)^*` preserving `D_QCoh` (Stacks 08F4).  The second is the full faithfulness of `ε^*` on
`D_QCoh`, the derived pullback along a morphism of schemes preserving `D_QCoh`
(Stacks 08DW (1)).

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.zariskiEtaleDerived_eq_representedDerivedAssociatedModule`: the
  spelling bridge, `ε^*` of `RelativeDescentHomDescentZariski.lean` is
  `AlgebraicGeometry.Space.representedDerivedAssociatedModule`.
* `AlgebraicGeometry.Space.exists_zariskiEtaleDerived_iso`: every object of `D_QCoh(𝒪_{h_T})` is
  `ε^*ω` for some `ω ∈ D_QCoh(𝒪_T)`.
* `AlgebraicGeometry.Space.bijective_zariskiEtaleDerived_map`: `ε^*` is bijective on morphisms
  between objects of `D_QCoh(𝒪_T)`.
* `RepresentedDerivedPullbackComparison.bijective_homMap_of_isQuasicoherent`:
  `Φ.homMap g K L` is bijective for `K, L ∈ D_QCoh`, for every comparison datum `Φ`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.exists_zariskiEtaleDerived_iso_modelInitial`
  and `exists_zariskiEtaleDerived_iso_restrict`: piece (i) at the model of `X₀`, and at the model
  of an étale `U₀ ⟶ X₀` in the restricted situation.
* `RelativeDescentSituation.homDescent_of_zariskiModelHomDescent_of_quasicoherent`:
  the conclusion of Stacks 0DKV for `K, L ∈ D_QCoh(𝒪_{X₀})`, `X₀` affine, from the Zariski form
  for every pair `(K'', L'')` of `D_QCoh(𝒪_{Z'})` with `ε^*K'' ≅ L(e₀)^*K`, `ε^*L'' ≅ L(e₀)^*L`.

## Implementation notes

As in `RelativeDescentHomDescentZariski.lean`, everything is stated for an arbitrary
pseudofunctoriality datum `P` and an arbitrary comparison datum `Φ`, in the instance environment
of `RelativeDescentHomDescentModel.lean`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u v

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The spelling bridge.**  The functor `ε^*` of `RelativeDescentHomDescentZariski.lean`, with
its categories of modules spelled as in the derived pullbacks, is
`AlgebraicGeometry.Space.representedDerivedAssociatedModule`. -/
theorem zariskiEtaleDerived_eq_representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    zariskiEtaleDerived B S hS T = representedDerivedAssociatedModule B S hS T :=
  rfl

/-- **Essential surjectivity of `ε^*` on `D_QCoh`** (Stacks 071Q): every object of `D(𝒪_{h_T})`
with quasi-coherent cohomology is `ε^*ω` for some `ω ∈ D(𝒪_T)` with quasi-coherent cohomology. -/
theorem exists_zariskiEtaleDerived_iso (T : BigFppfOver B S hS)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace T))))
    (hM : IsInQuasicoherentDerived (schemeSpace T) M) :
    ∃ ω : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
          ω).IsQuasicoherent) ∧
        Nonempty ((zariskiEtaleDerived B S hS T).obj ω ≅ M) :=
  exists_representedDerivedAssociatedModule_iso B S hS T M hM

/-- **Full faithfulness of `ε^*` on `D_QCoh`** (Stacks 071Q): `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})` is
bijective on morphisms between objects with quasi-coherent cohomology.  It is the composite of
the equivalence `ε^* : D_QCoh(𝒪_T) ⥤ D_QCoh(T_étale, 𝒪)`
(`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`) with the equivalence
`D(T_étale, 𝒪) ≌ D(𝒪_{h_T})` of the identification of the two small étale sites. -/
theorem bijective_zariskiEtaleDerived_map (T : BigFppfOver B S hS)
    (ω ω' : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hω : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        ω).IsQuasicoherent)
    (hω' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        ω').IsQuasicoherent) :
    Function.Bijective (fun φ : ω ⟶ ω' => (zariskiEtaleDerived B S hS T).map φ) := by
  have := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  have : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor).Additive :=
    additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteLimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
    preservesFiniteLimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteColimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
    preservesFiniteColimits_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)
  let c := Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (representedSmallEtaleModuleEquivalence B S hS T).functor
  let F := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let ω₀ : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory := ⟨ω, hω⟩
  let ω₀' : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory := ⟨ω', hω'⟩
  have h₁ : Function.Bijective (fun f : ω₀ ⟶ ω₀' => F.map f) :=
    (Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _
  have h₂ : Function.Bijective (fun ψ : F.obj ω₀ ⟶ F.obj ω₀' => (ObjectProperty.ι _).map ψ) :=
    (ObjectProperty.fullyFaithfulι _).map_bijective _ _
  have h₃ := (representedDerivedModuleEquivalence B S hS T).fullyFaithfulFunctor.map_bijective
    ((ObjectProperty.ι _).obj (F.obj ω₀)) ((ObjectProperty.ι _).obj (F.obj ω₀'))
  have key : (fun φ : ω ⟶ ω' => (zariskiEtaleDerived B S hS T).map φ) =
      ((c.app ω).homCongr (c.app ω')) ∘
        (fun χ => (representedDerivedModuleEquivalence B S hS T).functor.map χ) ∘
        (fun ψ : F.obj ω₀ ⟶ F.obj ω₀' => (ObjectProperty.ι _).map ψ) ∘
        (fun f : ω₀ ⟶ ω₀' => F.map f) ∘
        ((ObjectProperty.fullyFaithfulι _).homEquiv (X := ω₀) (Y := ω₀')).symm := by
    funext φ
    simp only
    exact (Iso.eq_inv_comp (c.app ω)).2 (c.hom.naturality φ).symm
  rw [key]
  exact ((c.app ω).homCongr (c.app ω')).bijective.comp (h₃.comp (h₂.comp (h₁.comp
    (ObjectProperty.fullyFaithfulι _).homEquiv.symm.bijective)))

namespace RepresentedDerivedPullbackComparison

variable {B S hS} {P : DerivedPullbackComposition B S hS}
  (Φ : RepresentedDerivedPullbackComparison B S hS P)

/-- **`ε^*` is bijective on the derived homomorphisms of the pullbacks of objects of `D_QCoh`**:
for `K, L ∈ D_QCoh(𝒪_T)` and every morphism `g : T' ⟶ T` of the site, `Φ.homMap g K L` is
bijective.  The derived pullback `Lg^*` preserves `D_QCoh` (Stacks 08DW (1),
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`), and `ε^*` is fully faithful
on `D_QCoh` (Stacks 071Q, `AlgebraicGeometry.Space.bijective_zariskiEtaleDerived_map`). -/
theorem bijective_homMap_of_isQuasicoherent {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (K L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        K).IsQuasicoherent)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        L).IsQuasicoherent) :
    Function.Bijective (Φ.homMap g K L) :=
  (Φ.bijective_homMap_iff g K L).2 (bijective_zariskiEtaleDerived_map B S hS T' _ _
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ K hK)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ L hL))

end RepresentedDerivedPullbackComparison

namespace RelativeDescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] {D : RelativeDescentSituation B S hS hZ I} {Z' : BigAffineFppf B S hS}

/-- **The pullback of an object of `D_QCoh(𝒪_{X₀})` to the model of `X₀` is `ε^*` of an object
of `D_QCoh(𝒪_{Z'})`.**  `L(e₀)^*` preserves `D_QCoh` (Stacks 08F4), and `ε^*` is essentially
surjective onto `D_QCoh` (Stacks 071Q). -/
theorem exists_zariskiEtaleDerived_iso_modelInitial
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ D.X₀) (K : D.InitialDerived)
    (hK : IsInQuasicoherentDerived D.initialSource K) :
    ∃ K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)) i).obj K'').IsQuasicoherent) ∧
        Nonempty ((zariskiEtaleDerived B S hS _).obj K'' ≅
          (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K) :=
  exists_zariskiEtaleDerived_iso B S hS _ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS _ K hK)

/-- **Piece (i) of the affine leaf of Stacks 0DKV.**  In the situation restricted along a flat
finitely presented `u : U₀ ⟶ X₀` (in the proof of the tag, étale with `U₀` affine), with
`e₀ : yoneda Z' ≅ U₀`, the pullback `L(e₀)^*Lu^*K₀` of an object `K₀ ∈ D_QCoh(𝒪_{X₀})` is
`ε^*K''` for an object `K''` of `D_QCoh(𝒪_{Z'})`: both pullbacks preserve `D_QCoh`
(Stacks 08F4) and `ε^*` is essentially surjective onto `D_QCoh` (Stacks 071Q). -/
theorem exists_zariskiEtaleDerived_iso_restrict {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀) (hgflat : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g)
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅
      (D.restrict hU₀ g hgflat hgfp).X₀)
    (K₀ : D.InitialDerived) (hK₀ : IsInQuasicoherentDerived D.initialSource K₀) :
    ∃ K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)) i).obj K'').IsQuasicoherent) ∧
        Nonempty ((zariskiEtaleDerived B S hS _).obj K'' ≅
          (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj
            ((smallEtaleDerivedModulePullback B S hS
              (D.restrictInitial hU₀ g hgflat hgfp)).obj K₀)) :=
  exists_zariskiEtaleDerived_iso_modelInitial e₀ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS _ K₀ hK₀)

variable {P : DerivedPullbackComposition B S hS} (Φ : RepresentedDerivedPullbackComparison B S hS P)
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ D.X₀}
  (R₀ : D.AffineBaseChangeRepresentation Z' (e₀.hom ≫ D.p₀))

include Φ in
/-- **Stacks 0DKV for a situation with affine `X₀` and `K, L ∈ D_QCoh(𝒪_{X₀})`, from the Zariski
form on its affine model**: pieces (i) and (ii) of the affine leaf discharged.  It suffices that
`ZariskiModelHomDescent R₀ K'' L''` holds for every pair `K'', L'' ∈ D_QCoh(𝒪_{Z'})` with
`ε^*K'' ≅ L(e₀)^*K` and `ε^*L'' ≅ L(e₀)^*L`; such a pair exists by
`exists_zariskiEtaleDerived_iso_modelInitial`, and `ε^*` is bijective on the derived
homomorphisms of its pullbacks to the stages and to the limit by
`RepresentedDerivedPullbackComparison.bijective_homMap_of_isQuasicoherent`. -/
theorem homDescent_of_zariskiModelHomDescent_of_quasicoherent (K L : D.InitialDerived)
    (hK : IsInQuasicoherentDerived D.initialSource K)
    (hL : IsInQuasicoherentDerived D.initialSource L)
    (H : ∀ K'' L'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)) i).obj K'').IsQuasicoherent) →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)) i).obj L'').IsQuasicoherent) →
      ((zariskiEtaleDerived B S hS _).obj K'' ≅
        (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K) →
      ((zariskiEtaleDerived B S hS _).obj L'' ≅
        (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj L) →
      ZariskiModelHomDescent R₀ K'' L'') :
    D.HomDescent P K L := by
  obtain ⟨K'', hK'', ⟨a⟩⟩ := exists_zariskiEtaleDerived_iso_modelInitial e₀ K hK
  obtain ⟨L'', hL'', ⟨b⟩⟩ := exists_zariskiEtaleDerived_iso_modelInitial e₀ L hL
  exact homDescent_of_zariskiModelHomDescent Φ R₀ K L a b
    (fun j => Φ.bijective_homMap_of_isQuasicoherent (R₀.q j) K'' L'' hK'' hL'')
    (Φ.bijective_homMap_of_isQuasicoherent R₀.qc K'' L'' hK'' hL'') (H K'' L'' hK'' hL'' a b)

end RelativeDescentSituation

end AlgebraicGeometry.Space
