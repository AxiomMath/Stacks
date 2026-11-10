module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingPair
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.PullbackIsoInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.OverEquivInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingModelSliceSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTranspose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
import StacksCore.Tactic.StacksAttribute

/-!
# Two dualizing complexes over an affine open, read on the slice site

Let `X` be a locally Noetherian scheme, `V ⊆ X` an affine open and `K`, `K'` dualizing complexes
on `X` ([Stacks, Tag 0A87]). This file proves, on the slice site `Opens(X)/V` — the model in which
restriction to a member of a covering family is phrased — the two affine-local inputs of
[Stacks, Tag 0ATP]:

* the evaluation morphism `R𝓗om(K|_V, K'|_V) ⊗^𝐋 K|_V ⟶ K'|_V` of [Stacks, Tag 08J8] is an
  isomorphism, and
* `R𝓗om(K|_V, K'|_V)` is an invertible object of `D(𝒪_X|_V)`.

Over `Spec Γ(X, V)` both are the affine case of [Stacks, Tag 0A7F]. They are carried to the slice
site along the two equivalences that `Stacks.Duality.HasDualizingModelOn` seals: the pullback along
`V ≅ Spec Γ(X, V)` and the equivalence `Scheme.Modules.overEquiv V` between modules on the open
subscheme and on the slice site. Along an equivalence carrying tensor products to tensor products
the derived internal hom is carried to the derived internal hom and the evaluation morphism to the
evaluation morphism; that is
`CategoryTheory.InternalHomTransfer.exists_iso_and_isIso_iff_of_equivalence`, whose only input is
the tensor comparison, naturally in the first variable.

## Main results

* `Stacks.Duality.isInvertible_derivedSheafHom_derivedTilde`: over `Spec R`, `R𝓗om(ω̃, ω̃')` is
  invertible for two dualizing complexes `ω`, `ω'` over a Noetherian ring `R`.
* `Stacks.SheafOfModules.PullbackIsoTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff`: the
  pullback along an isomorphism of schemes carries the derived internal hom and the evaluation
  morphism of [Stacks, Tag 08DI].
* `Stacks.SheafOfModules.OverEquivTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff`: so does
  `overEquiv U`, from the slice site to the open subscheme.
* `Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`: **the two
  affine-local inputs of [Stacks, Tag 0ATP] on the slice site.**

## Implementation notes

Every transport is stated once over variables and only instantiated in the final statements:
at the concrete objects the elaborator cannot afford to compare the several spellings of the
categories involved, which agree only after unfolding. For the same reason the abelian structures
on the categories of modules of the slice site and of the open subscheme are named once, as local
instances, at the top of the file.

## References

* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- Sheafification on the site of opens of a scheme, supplied directly. -/
local instance hasSheafifyOpensScheme (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- Sheafification on a slice of the site of opens of a scheme, supplied directly. -/
local instance hasSheafifyOverOpens (X : Scheme.{u}) (U : X.Opens) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := inferInstance

/-- Sheaves of modules on the slice site `Opens(X)/U` form an abelian category, supplied as a
term: instance search does not find it once the pullback comparisons are in scope. -/
local instance abelianSlice (X : Scheme.{u}) (U : X.Opens) :
    Abelian (Stacks.SheafOfModules.DerivedMonoidal.Mod
      (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X U)) :=
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
    (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X U)

/-- Sheaves of modules on an open subscheme form an abelian category, supplied as a term. -/
local instance abelianOpen (X : Scheme.{u}) (U : X.Opens) :
    Abelian (Stacks.SheafOfModules.DerivedMonoidal.Mod
      (Stacks.SheafOfModules.OverEquivTensor.openRingSheaf X U)) :=
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
    (Stacks.SheafOfModules.OverEquivTensor.openRingSheaf X U)

/-- Sheaves of modules on the slice ringed site form an abelian category, supplied as a term. -/
local instance abelianSliceSite (X : Scheme.{u}) (U : X.Opens) :
    Abelian (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U).O)) :=
  abelianSlice X U

namespace AlgebraicGeometry.RingedSite

/-- **The derived internal hom of a ringed site is an internal hom through its evaluation
morphism**: `g ↦ (g ⊗^𝐋 1) ≫ e` is the bijection of [Stacks, Tag 08J8]
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`). -/
theorem tensorHomBijective_derivedSheafHomCounit (Y : RingedSite.{u, u, u})
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
    [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ)]
    (L M Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    Function.Bijective (fun g : Z ⟶ ((derivedSheafHomBifunctor Y).obj (op L)).obj M =>
      ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).map g).app L ≫
        derivedSheafHomCounit Y L M) := by
  have hfun : (fun g : Z ⟶ ((derivedSheafHomBifunctor Y).obj (op L)).obj M =>
        ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).map g).app L ≫
          derivedSheafHomCounit Y L M) = ⇑(derivedCurryHomEquiv Y Z L M) :=
    funext fun g => (derivedCurryHomEquiv_apply Y Z L M g).symm
  rw [hfun]
  exact (derivedCurryHomEquiv Y Z L M).bijective

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

/-- **The derived internal hom of a ringed space is an internal hom through its evaluation
morphism**, with the tensor product written as the bifunctor `Stacks.SheafOfModules.derivedTensor`
rather than through a monoidal structure. This is
`Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit` without the monoidal structure:
`g ↦ (g ⊗^𝐋 1) ≫ e` is the bijection of [Stacks, Tag 08DI], by the naturality of that bijection
in its source variable at the identity. -/
theorem tensorHomBijective_derivedSheafHomCounit' {X : TopCat.{u}}
    (Rc : TopCat.Sheaf CommRingCat.{u} X)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]
    (K M Z : DerivedCategory (StructureSheafModules Rc)) :
    Function.Bijective fun a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
      ((derivedTensor Rc).map a).app K ≫ derivedSheafHomCounit Rc K M := by
  have hfun : (fun a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
        ((derivedTensor Rc).map a).app K ≫ derivedSheafHomCounit Rc K M) =
      ⇑(derivedSheafHomTensorEquiv Rc Z K M) := by
    funext a
    have hnat : ∀ (b : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M)
        (g : ((derivedSheafHom Rc).obj (op K)).obj M ⟶ ((derivedSheafHom Rc).obj (op K)).obj M),
        RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M (b ≫ g) =
          ((derivedTensor Rc).map b).app K ≫ RingedSite.derivedCurryHomEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op K)).obj M) K M g :=
      fun b g => RingedSite.derivedCurryHomEquiv_naturality_source (ringedSite Rc) b g
    have hcounit : derivedSheafHomCounit Rc K M =
        RingedSite.derivedCurryHomEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op K)).obj M) K M
          (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) := rfl
    rw [hcounit]
    have h0 := hnat a (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M))
    exact h0.symm.trans
      (congrArg (fun v : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
        RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M v) (Category.comp_id a))
  rw [hfun]
  exact (derivedSheafHomTensorEquiv Rc Z K M).bijective

end Stacks.SheafOfModules

namespace Stacks.Duality

variable (R : CommRingCat.{u})

/-- **The derived internal hom between two dualizing complexes on an affine scheme is
invertible.** Let `R` be a Noetherian ring and `ω`, `ω'` dualizing complexes for `R`. Then
`R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃')` is an invertible object of `D(𝒪_{Spec R})`.

Write `ω̃' ≅ ω̃ ⊗^𝐋 P` with `P` invertible
(`Stacks.Duality.exists_isInvertible_tensor_iso_derivedTildeStandard`). The unit is an internal
hom from `ω̃` to `ω̃` through the left unitor
(`Stacks.Duality.tensorHomBijective_tensorUnit_derivedTilde`), so `𝟙 ⊗ P` is one from `ω̃` to
`ω̃ ⊗ P`, and two internal homs for one pair are isomorphic. -/
theorem isInvertible_derivedSheafHom_derivedTilde [IsNoetherianRing R]
    {ω ω' : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω') :
    letI := derivedMonoidalStructure (Spec R).sheaf
    IsInvertible (((derivedSheafHom (Spec R).sheaf).obj
      (op ((derivedTildeStructureSheafModules R).obj ω))).obj
        ((derivedTildeStructureSheafModules R).obj ω')) := by
  let := derivedMonoidalStructure (Spec R).sheaf
  let := derivedSymmetricStructure (Spec R).sheaf
  obtain ⟨P, hP, ⟨u⟩⟩ := exists_isInvertible_tensor_iso_derivedTildeStandard R hω hω'
  set A := (derivedTildeStructureSheafModules R).obj ω
  set A' := (derivedTildeStructureSheafModules R).obj ω'
  have h1 := tensorHomBijective_tensorUnit_derivedTilde R hω
  have h2 := tensorHomBijective_whiskerRight_of_isInvertible ((λ_ A).hom) h1 hP
  have h3 := tensorHomBijective_comp_iso
    ((tensorRightComm P A).hom.app (𝟙_ _) ≫ (λ_ A).hom ▷ P) u h2
  obtain ⟨e, -⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective
    (((tensorRightComm P A).hom.app (𝟙_ _) ≫ (λ_ A).hom ▷ P) ≫ u.hom)
    (derivedSheafHomCounit (Spec R).sheaf A A') h3
    (tensorHomBijective_derivedSheafHomCounit (Spec R).sheaf A A')
  exact MonoidalCategory.isInvertible_of_iso ((λ_ P).symm ≪≫ e) hP

end Stacks.Duality

namespace Stacks.SheafOfModules.PullbackIsoTensor

open CochainComplex.KFlatBifunctor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- **`f^*` as an equivalence of derived categories**, for an isomorphism `f` of schemes. -/
abbrev pullbackDerivedEquivalence :
    DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)) ≌
      DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf X)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (pullbackEquivMod f)

/-- **`f^*(K ⊗^𝐋 L) ≅ f^*K ⊗^𝐋 f^*L` as an isomorphism of bifunctors**, at the derived tensor
product the tensor–internal-hom bijection of [Stacks, Tag 08J8] is stated at: the transport
along `f^*` of `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`, conjugated by
the comparison `Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge` of the two derived
tensor products on each side. -/
def pullbackDerivedTensorNatIso :
    derivedTensor Y.sheaf ⋙ (Functor.whiskeringRight _ _ _).obj
        (pullbackDerivedEquivalence f).functor ≅
      (pullbackDerivedEquivalence f).functor ⋙ derivedTensor X.sheaf ⋙
        (Functor.whiskeringLeft _ _ _).obj (pullbackDerivedEquivalence f).functor :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge (ringedSite Y.sheaf)).symm _ ≪≫
    derivedTransportIsoOfEquivalence (modTensor Y) (modTensor X) (pullbackEquivMod f)
      (pullbackTensorIso f)
      (fun v B => pullbackTensorIso_naturality_left f v B)
      (fun A {_ _} w => pullbackTensorIso_naturality_right f A w) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge (ringedSite X.sheaf)) _)

end Stacks.SheafOfModules.PullbackIsoTensor

namespace Stacks.SheafOfModules.OverEquivTensor

open CochainComplex.KFlatBifunctor
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)

variable (X : Scheme.{u}) (U : X.Opens)

/-- **`overEquiv U` as an equivalence of derived categories**, between the slice site
`Opens(X)/U` and the open subscheme `U`. -/
abbrev overEquivDerivedEquivalence :
    DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (sliceRingSheaf X U)) ≌
      DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (openRingSheaf X U)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (overEquivMod X U)

/-- **`e(K ⊗^𝐋 L) ≅ e K ⊗^𝐋 e L` as an isomorphism of bifunctors** for `e = overEquiv U`, at the
derived tensor products the tensor–internal-hom bijection of [Stacks, Tag 08J8] is stated at, on
the slice site and on the open subscheme. -/
def overEquivDerivedTensorNatIso :
    Stacks.SheafOfModules.derivedTensorProductFunctor
          ((Stacks.SheafOfModules.ringedSite X.sheaf).over U) ⋙
        (Functor.whiskeringRight _ _ _).obj (overEquivDerivedEquivalence X U).functor ≅
      (overEquivDerivedEquivalence X U).functor ⋙ derivedTensor U.toScheme.sheaf ⋙
        (Functor.whiskeringLeft _ _ _).obj (overEquivDerivedEquivalence X U).functor :=
  by
  have sourceComparison := Functor.isoWhiskerRight
      (Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)).symm
      ((Functor.whiskeringRight _ _ _).obj (overEquivDerivedEquivalence X U).functor)
  have transported :=
    derivedTransportIsoOfEquivalence (sheafTensor.{u, u, u, u, u} (sliceRingSheaf X U))
      (sheafTensor.{u, u, u, u, u} (openRingSheaf X U)) (overEquivMod X U)
      (overEquivTensorIso X U)
      (fun f B => overEquivTensorIso_naturality_left X U f B)
      (fun A {_ _} g => overEquivTensorIso_naturality_right X U A g)
  have targetComparison := Functor.isoWhiskerLeft (overEquivDerivedEquivalence X U).functor
    (Functor.isoWhiskerRight
      (Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge
        (Stacks.SheafOfModules.ringedSite U.toScheme.sheaf))
      ((Functor.whiskeringLeft _ _ _).obj (overEquivDerivedEquivalence X U).functor))
  exact sourceComparison ≪≫ transported ≪≫ targetComparison

end Stacks.SheafOfModules.OverEquivTensor

namespace CategoryTheory.MonoidalCategory

/-- **Invertibility depends only on the tensor products of objects and on the unit**: if two
monoidal structures on one category have pairwise isomorphic tensor products and isomorphic
units, an object invertible for the first is invertible for the second. No coherence and no
braiding is used. -/
theorem isInvertible_of_tensorIso_of_unitIso {C : Type*} [Category C]
    (m₁ m₂ : MonoidalCategory C)
    (μ : ∀ A B : C, (@MonoidalCategoryStruct.tensorObj C _ m₁.toMonoidalCategoryStruct A B) ≅
      (@MonoidalCategoryStruct.tensorObj C _ m₂.toMonoidalCategoryStruct A B))
    (ε : (@MonoidalCategoryStruct.tensorUnit C _ m₁.toMonoidalCategoryStruct) ≅
      (@MonoidalCategoryStruct.tensorUnit C _ m₂.toMonoidalCategoryStruct))
    {X : C} (h : @IsInvertible C _ m₁ X) : @IsInvertible C _ m₂ X := by
  obtain ⟨hX⟩ := h
  exact ⟨@HasInverse.mk C _ m₂ X (@HasInverse.inv C _ m₁ X hX)
    ((μ X _).symm ≪≫ @HasInverse.isoLeft C _ m₁ X hX ≪≫ ε)
    ((μ _ X).symm ≪≫ @HasInverse.isoRight C _ m₁ X hX ≪≫ ε)⟩

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules.PullbackIsoTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- **The pullback along an isomorphism of schemes carries the derived internal hom and the
evaluation morphism of [Stacks, Tag 08DI].** For objects `A`, `B` of `D(𝒪_Y)`,
`f^* R𝓗om(A, B) ≅ R𝓗om(f^*A, f^*B)`, and the evaluation morphism at `(A, B)` is an isomorphism
exactly when the one at `(f^*A, f^*B)` is. -/
theorem exists_iso_and_isIso_derivedSheafHomCounit_iff
    (A B : DerivedCategory (StructureSheafModules Y.sheaf)) :
    Nonempty ((pullbackEquivMod f).functor.mapDerivedCategory.obj
        (((derivedSheafHom Y.sheaf).obj (op A)).obj B) ≅
      ((derivedSheafHom X.sheaf).obj
        (op ((pullbackEquivMod f).functor.mapDerivedCategory.obj A))).obj
          ((pullbackEquivMod f).functor.mapDerivedCategory.obj B)) ∧
      (IsIso (derivedSheafHomCounit Y.sheaf A B) ↔
        IsIso (derivedSheafHomCounit X.sheaf ((pullbackEquivMod f).functor.mapDerivedCategory.obj A)
          ((pullbackEquivMod f).functor.mapDerivedCategory.obj B))) :=
  CategoryTheory.InternalHomTransfer.exists_iso_and_isIso_iff_of_equivalence_of_natIso
    (derivedTensor Y.sheaf) (derivedTensor X.sheaf) (pullbackDerivedEquivalence f)
    (pullbackDerivedTensorNatIso f) (derivedSheafHomCounit Y.sheaf A B)
    (tensorHomBijective_derivedSheafHomCounit' Y.sheaf A B)
    (derivedSheafHomCounit X.sheaf _ _) (tensorHomBijective_derivedSheafHomCounit' X.sheaf _ _)

end Stacks.SheafOfModules.PullbackIsoTensor

namespace Stacks.SheafOfModules.OverEquivTensor

variable (X : Scheme.{u}) (U : X.Opens)

/-- **`overEquiv U` carries the derived internal hom and the evaluation morphism of
[Stacks, Tag 08J8] of the slice site `Opens(X)/U` to those of the open subscheme `U`.** For
objects `A`, `B` of `D(𝒪_X|_U)` on the slice site, `e R𝓗om(A, B) ≅ R𝓗om(e A, e B)`, and the
evaluation morphism at `(A, B)` is an isomorphism exactly when the one at `(e A, e B)` is. -/
theorem exists_iso_and_isIso_derivedSheafHomCounit_iff
    (A B : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U).O))) :
    Nonempty ((overEquivMod X U).functor.mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor
          ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)).obj (op A)).obj B) ≅
      ((derivedSheafHom U.toScheme.sheaf).obj
        (op ((overEquivMod X U).functor.mapDerivedCategory.obj A))).obj
          ((overEquivMod X U).functor.mapDerivedCategory.obj B)) ∧
      (IsIso (RingedSite.derivedSheafHomCounit
          ((Stacks.SheafOfModules.ringedSite X.sheaf).over U) A B) ↔
        IsIso (derivedSheafHomCounit U.toScheme.sheaf
          ((overEquivMod X U).functor.mapDerivedCategory.obj A)
          ((overEquivMod X U).functor.mapDerivedCategory.obj B))) :=
  CategoryTheory.InternalHomTransfer.exists_iso_and_isIso_iff_of_equivalence_of_natIso
    _ (derivedTensor U.toScheme.sheaf) (overEquivDerivedEquivalence X U)
    (overEquivDerivedTensorNatIso X U)
    (RingedSite.derivedSheafHomCounit ((Stacks.SheafOfModules.ringedSite X.sheaf).over U) A B)
    (RingedSite.tensorHomBijective_derivedSheafHomCounit _ A B)
    (derivedSheafHomCounit U.toScheme.sheaf _ _)
    (tensorHomBijective_derivedSheafHomCounit' U.toScheme.sheaf _ _)

/-- **`overEquiv U` reflects invertibility into the slice site**, read at the re-seated monoidal
structure `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` of the slice site, whose tensor
product is the derived tensor product of [Stacks, Tag 08J8] on the nose. -/
theorem isInvertible_derivedTensorMonoidal_of_isInvertible_overEquiv
    (A : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U).O)))
    (hA : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (openRingSheaf X U)
      MonoidalCategory.IsInvertible ((overEquivMod X U).functor.mapDerivedCategory.obj A)) :
    letI := RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)
    MonoidalCategory.IsInvertible A := by
  have h := isInvertible_of_isInvertible_overEquiv X U A hA
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (sliceRingSheaf X U)) _ _
      (RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over U))
      (RingedSite.derivedTensorSymmetric
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)).toBraidedCategory
      (𝟭 _)
      (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso
        (sliceRingSheaf X U)
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)))).app A).app B)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (sliceRingSheaf X U)) A h

/-- **Invertibility reflected into the slice site from an isomorphic object of `D(𝒪_U)`**: if
`e A ≅ L` for an invertible `L` on the open subscheme, then `A` is invertible on the slice site,
at the re-seated monoidal structure there. -/
theorem isInvertible_derivedTensorMonoidal_of_iso
    (A : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U).O)))
    {L : DerivedCategory (_root_.SheafOfModules.{u} (PullbackIsoTensor.modRingSheaf U.toScheme))}
    (hL : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal U.toScheme.sheaf
      MonoidalCategory.IsInvertible L)
    (e : (overEquivMod X U).functor.mapDerivedCategory.obj A ≅ L) :
    letI := RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)
    MonoidalCategory.IsInvertible A := by
  have h := @MonoidalCategory.isInvertible_of_iso _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (openRingSheaf X U)) _ _ e.symm hL
  exact isInvertible_derivedTensorMonoidal_of_isInvertible_overEquiv X U A h

end Stacks.SheafOfModules.OverEquivTensor

namespace Stacks.SheafOfModules

/-- **The evaluation morphism of [Stacks, Tag 08DI] at isomorphic pairs**: for `A ≅ A'` and
`B ≅ B'` in `D(𝒪_X)`, `R𝓗om(A, B) ≅ R𝓗om(A', B')` and the evaluation morphism at `(A, B)` is an
isomorphism exactly when the one at `(A', B')` is. -/
theorem exists_iso_and_isIso_derivedSheafHomCounit_iff_of_iso {X : TopCat.{u}}
    (Rc : TopCat.Sheaf CommRingCat.{u} X)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]
    {A A' B B' : DerivedCategory (StructureSheafModules Rc)} (a : A ≅ A') (b : B ≅ B') :
    Nonempty (((derivedSheafHom Rc).obj (op A)).obj B ≅ ((derivedSheafHom Rc).obj (op A')).obj B')
      ∧ (IsIso (derivedSheafHomCounit Rc A B) ↔ IsIso (derivedSheafHomCounit Rc A' B')) :=
  CategoryTheory.InternalHomTransfer.exists_iso_and_isIso_iff_of_iso (derivedTensor Rc) a b
    (derivedSheafHomCounit Rc A B) (tensorHomBijective_derivedSheafHomCounit' Rc A B)
    (derivedSheafHomCounit Rc A' B') (tensorHomBijective_derivedSheafHomCounit' Rc A' B')

end Stacks.SheafOfModules

namespace Stacks.Duality

/-- **Invertibility carried from `Spec Γ(X, V)` to the slice site over an affine open `V`**: along
the pullback by `V ≅ Spec Γ(X, V)` and then, reflected, along `overEquiv V`, at the re-seated
monoidal structure of the slice site. -/
theorem isInvertible_derivedTensorMonoidal_of_iso_pullback
    {W : Scheme.{u}} (V : W.Opens) (hV : IsAffineOpen V)
    (M : DerivedCategory (StructureSheafModules (Spec Γ(W, V)).sheaf))
    (A : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite W.sheaf).over V).O)))
    (hM : @MonoidalCategory.IsInvertible _ _
      (DerivedMonoidal.derivedMonoidal (Spec Γ(W, V)).sheaf) M)
    (t : (PullbackIsoTensor.pullbackEquivMod hV.isoSpec.hom).functor.mapDerivedCategory.obj M ≅
      (OverEquivTensor.overEquivMod W V).functor.mapDerivedCategory.obj A) :
    letI := RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite W.sheaf).over V)
    MonoidalCategory.IsInvertible A := by
  have hI₂ := PullbackIsoTensor.isInvertible_pullback hV.isoSpec.hom M hM
  exact OverEquivTensor.isInvertible_derivedTensorMonoidal_of_iso W V A hI₂ t.symm

/-- The affine-local inputs of [Stacks, Tag 0ATP] on the slice site over an affine open `V`, from
the two dualizing models of `Stacks.Duality.HasDualizingModelOn` carried behind the slice-site
restriction. This is the body of
`Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`, stated with the
Noetherian hypothesis on `Γ(X, V)` as an instance argument and no hypothesis on `X`. -/
theorem isIso_derivedSheafHomCounit_restrictD_of_iso
    {W : Scheme.{u}} (V : W.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(W, V)]
    {ω ω' : DerivedCategory (ModuleCat.{u} Γ(W, V))}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω')
    (K K' : DerivedCategory W.Modules)
    (i : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} W.ringCatSheaf V).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(W, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω)
    (i' : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} W.ringCatSheaf V).mapDerivedCategory.obj K') ≅
      (tilde.functor Γ(W, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω') :
    IsIso (RingedSite.derivedSheafHomCounit ((ringedSite W.sheaf).over V)
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K')) ∧
      (letI := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V);
        IsInvertible (((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj
            K))).obj
            ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj
              K'))) := by
  have a := i ≪≫ (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(W, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app ω ≪≫
    (PullbackIsoTensor.restrictFunctorDerivedIsoPullback hV.isoSpec.hom).app
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
  have a' := i' ≪≫ (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(W, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app ω' ≪≫
    (PullbackIsoTensor.restrictFunctorDerivedIsoPullback hV.isoSpec.hom).app
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω')
  have h₁ := PullbackIsoTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff
    hV.isoSpec.hom ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω')
  have hS : IsIso (derivedSheafHomCounit (Spec Γ(W, V)).sheaf
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω')) :=
    isIso_derivedSheafHomCounit_derivedTilde_pair Γ(W, V) hω hω'
  have h₂ := exists_iso_and_isIso_derivedSheafHomCounit_iff_of_iso V.toScheme.sheaf a a'
  have h₃ := OverEquivTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff W V
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K')
  refine ⟨h₃.2.2 (h₂.2.2 (h₁.2.1 hS)), ?_⟩
  -- invertibility over `Spec Γ(X, V)`, read at the monoidal structure of [Stacks, Tag 0FPT]
  have hI₀ := isInvertible_derivedSheafHom_derivedTilde Γ(W, V) hω hω'
  have hI₁ : @MonoidalCategory.IsInvertible _ _
      (DerivedMonoidal.derivedMonoidal (Spec Γ(W, V)).sheaf)
      (((derivedSheafHom (Spec Γ(W, V)).sheaf).obj
        (op ((derivedTildeStructureSheafModules Γ(W, V)).obj ω))).obj
          ((derivedTildeStructureSheafModules Γ(W, V)).obj ω')) :=
    @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (derivedMonoidalStructure (Spec Γ(W, V)).sheaf) _ _
      (DerivedMonoidal.derivedMonoidal (Spec Γ(W, V)).sheaf)
      (DerivedMonoidal.derivedSymmetric (Spec Γ(W, V)).sheaf).toBraidedCategory
      (𝟭 _)
      (fun A B => (((derivedTensorMonoidalIso (Spec Γ(W, V)).sheaf).app A).app B).symm)
      (DerivedMonoidal.canonicalUnitIso (Spec Γ(W, V)).sheaf).symm _ hI₀
  -- carried to the open subscheme `V`, moved along the dualizing models, and reflected to the
  -- slice site
  exact isInvertible_derivedTensorMonoidal_of_iso_pullback V hV _ _ hI₁
    (h₁.1.some ≪≫ h₂.1.some.symm ≪≫ h₃.1.some.symm)
/-- **The affine-local inputs of [Stacks, Tag 0ATP], on the slice site.** Let `X` be a locally
Noetherian scheme, `V ⊆ X` an affine open and `K`, `K'` dualizing complexes on `X`. Over the slice
site `Opens(X)/V`, the evaluation morphism `R𝓗om(K|_V, K'|_V) ⊗^𝐋 K|_V ⟶ K'|_V` of
[Stacks, Tag 08J8] is an isomorphism and `R𝓗om(K|_V, K'|_V)` is invertible.

Over `Spec Γ(X, V)` both are the affine case [Stacks, Tag 0A7F]
(`Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde_pair`,
`Stacks.Duality.isInvertible_derivedSheafHom_derivedTilde`). They are carried to the open
subscheme `V` along the pullback by `V ≅ Spec Γ(X, V)`, moved along the isomorphisms of
`Stacks.Duality.HasDualizingModelOn`, and carried to the slice site along `overEquiv V`. -/
theorem isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex
    {W : Scheme.{u}} [IsLocallyNoetherian W] (V : W.Opens) (hV : IsAffineOpen V)
    (K K' : DerivedCategory W.Modules)
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    IsIso (RingedSite.derivedSheafHomCounit ((ringedSite W.sheaf).over V)
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K')) ∧
      (letI := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V);
        IsInvertible (((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj
            K))).obj
            ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj
              K'))) := by
  let : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨ω, hω, ⟨i⟩⟩ := exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex V K hV hK
  obtain ⟨ω', hω', ⟨i'⟩⟩ :=
    exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex V K' hV hK'
  exact @isIso_derivedSheafHomCounit_restrictD_of_iso W V hV
    (IsLocallyNoetherian.component_noetherian ⟨V, hV⟩) ω ω' hω hω' K K' i i'

end Stacks.Duality

