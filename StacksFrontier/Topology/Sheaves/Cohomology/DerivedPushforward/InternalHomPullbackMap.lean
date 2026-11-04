module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of a derived internal hom

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K, L ∈ D(𝒪_Y)`.  Tag
08I3 is the canonical map

`Lh^* R𝓗om_{𝒪_Y}(K, L) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*L)`

in `D(𝒪_X)`.  It is constructed the way the source constructs it: by the tensor–internal-hom
bijection of Tag 08DI the map is the same datum as a map
`Lh^*R𝓗om(K, L) ⊗^L_{𝒪_X} Lh^*K ⟶ Lh^*L`, the source of that is `Lh^*(R𝓗om(K,L) ⊗^L_{𝒪_Y} K)`
by the monoidality of derived pullback (Tag 079U), and the evaluation
`R𝓗om(K,L) ⊗^L_{𝒪_Y} K ⟶ L` is the transpose of the identity of `R𝓗om(K,L)`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge`: the comparison of the two
  derived tensor products of Tag 06YU carried by this repository, as an isomorphism of
  bifunctors on `D(𝒪_Z) × D(𝒪_Z)`.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso`: Tag 079U transported to
  the derived tensor product the derived internal hom is stated at.
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`: the comparison
  `P(hom(A, B)) ⟶ hom(P A, P B)` for a functor between categories with internal hom and a
  monoidality comparison, which is the construction of Tag 08I3 over abstract data.
* `Stacks.Cohomology.DerivedInternalHomPullback.derivedEvaluation`: the evaluation
  `R𝓗om(K, L) ⊗^L_{𝒪_Y} K ⟶ L`, the transpose of the identity.
* `Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap`: **Tag 08I3**, the
  canonical map `Lh^*R𝓗om(K, L) ⟶ R𝓗om(Lh^*K, Lh^*L)`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_adjoint`: the transpose
  of the comparison is the monoidality comparison followed by the image of the evaluation.
  This is the recipe the source gives for Tag 08I3, and it pins the comparison down.
* `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridgeModel_eq`: on a pair of K-flat
  complexes the comparison of the two derived tensor products is the composite of their two
  K-flat comparisons, so it is the identity of `Tot(A ⊗_{𝒪_Z} B)` in disguise.

## Implementation notes

*Two derived tensor products.*  This repository carries two independent derived tensor products
on `D(𝒪_Z)`: `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, the construction
`derivedTensorProductConstruction` made opaque with `irreducible_def`, at which the monoidality of
derived pullback (Tag 079U, `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`)
is stated, and `Stacks.SheafOfModules.canonicalDerivedTensorProduct` of the associated ringed
site, the construction `derivedTensorProductOfExact` made opaque with `irreducible_def`, at which
the whole derived-internal-hom cluster — in particular the tensor–internal-hom bijection of
Tag 08DI, `Stacks.SheafOfModules.derivedSheafHomTensorEquiv` — is stated.  They are not equal,
and the two halves of the construction of Tag 08I3 are stated at different ones.
`tensorBridge` identifies them.  It is built exactly as Tag 079U itself,
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, is built: on a pair of K-flat
complexes both bifunctors are the total tensor complex, by the `comparison` field of each, and
`D(𝒪_Z) × D(𝒪_Z)` is the localization of the pairs of K-flat objects of the homotopy category at
the quasi-isomorphisms, which descends the identification to all pairs.  Nothing about either
tensor product beyond that field and its naturality is used.

*Where the recipe is proved.*  `Transpose.homComparison_adjoint` is the recipe, and
`derivedPullbackSheafHomMap` is by definition `Transpose.homComparison` at the derived
pullback, the two derived internal homs, the two derived tensor products, the two bijections of
Tag 08DI and the monoidality comparison, so the recipe holds of it.  The *instance* of
`Transpose.homComparison_adjoint` at those data is not stated separately: stating it names the
Tag 08DI bijection applied to `derivedPullbackSheafHomMap`, and type-checking the instantiated
statement exhausts the default recursion budget, also when the bijection is written as a bare
`Equiv` rather than an additive one, when one spelling of the category of module sheaves is
fixed, and when the three definitions are made reducible.  A consumer who needs the equation
instantiates `Transpose.homComparison_adjoint` itself.

*Why a bare morphism and not an isomorphism.*  The source has a map here, and only asserts it
is an isomorphism under hypotheses stated elsewhere; so `derivedPullbackSheafHomMap` is a
morphism and `pullbackTensorIso` is used in its inverse direction only.

*Conjugating a naturality square.*  `conjugate_naturality` carries an identification of
values from chosen cochain representatives of a pair of K-flat objects to the images of those
objects in the derived category, which is the one step the descent needs beyond the
`comparison_naturality` field.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same sheaf of rings by `rfl`, and
-- every statement here mixes them, since the derived pullback is named at the first spelling
-- and the derived internal hom at the second; unless the two hom types are recognised as equal
-- both at `implicit` transparency and by instance search, the additive structure of a hom group
-- in the derived category is not found.  `structureSheafRing` is `@[instance_reducible]`, which
-- already gives both, so it is not named here: a local `implicit_reducible` on it would only
-- take instance search away.  Its reduct stops at an explicit-constructor projection, while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`, so the two Mathlib
-- definitions bridging those are the ones that have to be unfolded.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

noncomputable section

/-! ### Conjugating a naturality square -/

/-- Conjugating an isomorphism of values by isomorphisms of the objects preserves a naturality
square.  This is the step that carries an identification from the chosen cochain
representatives of a pair of objects to the images of those objects in the derived category. -/
alias conjugate_naturality := Stacks.Cohomology.DerivedPullbackTensor.naturality_transport

/-- Two objects each identified with a third, compatibly with a morphism, are identified with
each other compatibly with that morphism.  This is the algebra of a comparison written as
`c₁ ≪≫ c₂.symm`: a naturality square for each of the two legs gives one for the composite. -/
theorem conjugate_comparison {E : Type*} [Category E] {P P' Q₁ Q₂ T T' : E}
    (u : P ⟶ P') (v : Q₁ ⟶ Q₂) (w : T ⟶ T')
    (c₁ : P ≅ T) (c₁' : P' ≅ T') (c₂ : Q₁ ≅ T) (c₂' : Q₂ ≅ T')
    (hl : u ≫ c₁'.hom = c₁.hom ≫ w) (hr : v ≫ c₂'.hom = c₂.hom ≫ w) :
    u ≫ (c₁' ≪≫ c₂'.symm).hom = (c₁ ≪≫ c₂.symm).hom ≫ v := by
  have key : w ≫ c₂'.inv = c₂.inv ≫ v := by
    apply (cancel_mono c₂'.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hr,
      Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hl, Category.assoc, key, Category.assoc]

/-! ### The transpose construction, over abstract data -/

namespace Transpose

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- The evaluation `hom(A, B) ⊗ A ⟶ B` of an internal hom carrying a tensor–hom bijection: the
transpose of the identity of `hom(A, B)`. -/
def evaluation (A B : D₁) : T₁.obj ((H₁.obj (op A)).obj B, A) ⟶ B :=
  e₁ ((H₁.obj (op A)).obj B) A B (𝟙 _)

/-- The transpose datum `P(hom(A, B)) ⊗ P A ⟶ P B` of the comparison of a functor with
internal hom: the monoidality comparison followed by `P` of the evaluation. -/
def homComparisonDatum (A B : D₁) :
    T₂.obj (P.obj ((H₁.obj (op A)).obj B), P.obj A) ⟶ P.obj B :=
  m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B)

/-- The comparison `P(hom(A, B)) ⟶ hom(P A, P B)` of a functor with internal hom: the
transpose, under the tensor–hom bijection in the target, of `homComparisonDatum`. -/
def homComparison (A B : D₁) :
    P.obj ((H₁.obj (op A)).obj B) ⟶ (H₂.obj (op (P.obj A))).obj (P.obj B) :=
  (e₂ (P.obj ((H₁.obj (op A)).obj B)) (P.obj A) (P.obj B)).symm
    (homComparisonDatum P H₁ T₁ T₂ e₁ m A B)

/-- The transpose of the comparison is the transpose datum.  The tensor–hom bijection being a
bijection, this pins the comparison down. -/
theorem homComparison_adjoint (A B : D₁) :
    e₂ (P.obj ((H₁.obj (op A)).obj B)) (P.obj A) (P.obj B)
        (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) =
      homComparisonDatum P H₁ T₁ T₂ e₁ m A B :=
  (e₂ (P.obj ((H₁.obj (op A)).obj B)) (P.obj A) (P.obj B)).apply_symm_apply _

end Transpose

/-! ### The two derived tensor products -/

variable (Z : RingedSpace.{u, u})

/-- The derived tensor product of Tag 06YU at which the monoidality of derived pullback,
Tag 079U, is stated. -/
abbrev pullbackTensorProduct :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Z.sheaf :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf

/-- The derived tensor product of Tag 06YU at which the derived internal hom and the
tensor–internal-hom bijection of Tag 08DI are stated. -/
abbrev internalHomTensorProduct :
    Stacks.SheafOfModules.DerivedTensorProduct (Stacks.SheafOfModules.ringedSite Z.sheaf) :=
  Stacks.SheafOfModules.canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite Z.sheaf)

/-- `- ⊗^L_{𝒪_Z} -` at the first of the two derived tensor products, as a functor on pairs. -/
abbrev pullbackTensorUncurried :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  Functor.uncurry.obj (pullbackTensorProduct Z).tensor

/-- `- ⊗^L_{𝒪_Z} -` at the second of the two derived tensor products, as a functor on pairs. -/
abbrev internalHomTensorUncurried :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  Functor.uncurry.obj (internalHomTensorProduct Z).tensor

/-- **The comparison of the two derived tensor products on K-flat representatives.**  Both are
the total tensor complex `Tot(A ⊗_{𝒪_Z} B)` there, by the `comparison` field of each. -/
def tensorBridgeModel
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B) :
    (pullbackTensorUncurried Z).obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≅
      (internalHomTensorUncurried Z).obj
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) :=
  (pullbackTensorProduct Z).comparison A B hA hB ≪≫
    ((internalHomTensorProduct Z).comparison A B hA hB).symm

/-- The comparison on K-flat representatives is the composite of the two K-flat comparisons. -/
theorem tensorBridgeModel_eq
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B) :
    (tensorBridgeModel Z A B hA hB).hom =
      ((pullbackTensorProduct Z).comparison A B hA hB).hom ≫
        ((internalHomTensorProduct Z).comparison A B hA hB).inv :=
  rfl

/-- The comparison on K-flat representatives is natural in cochain maps between them. -/
theorem tensorBridgeModel_naturality
    {A A' B B' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A') (b : B ⟶ B')
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hA' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A')
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B)
    (hB' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B') :
    (pullbackTensorUncurried Z).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (tensorBridgeModel Z A' B' hA' hB').hom =
      (tensorBridgeModel Z A B hA hB).hom ≫
        (internalHomTensorUncurried Z).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) := by
  have hl := (pullbackTensorProduct Z).comparison_naturality a b hA hA' hB hB'
  have hr := (internalHomTensorProduct Z).comparison_naturality a b hA hA' hB hB'
  rw [← Category.assoc] at hl hr
  exact conjugate_comparison _ _ _ _ _ _ _ hl hr

/-- **The comparison of the two derived tensor products on K-flat models, as an isomorphism of
functors** on pairs of K-flat objects of the homotopy category.  Its value at a pair is
`tensorBridgeModel`, transported along the `Q` versus `Qh ∘ quotient` bridge. -/
def tensorBridgeModels :
    kFlatQPair (Y := Z) ⋙ pullbackTensorUncurried Z ≅
      kFlatQPair (Y := Z) ⋙ internalHomTensorUncurried Z :=
  NatIso.ofComponents
    (fun M => (pullbackTensorUncurried Z).mapIso (kFlatQPairIso M) ≪≫
      tensorBridgeModel Z M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((internalHomTensorUncurried Z).mapIso (kFlatQPairIso M)).symm)
    (fun {M N} g => by
      refine conjugate_naturality _ _ (kFlatQPairIso M) (kFlatQPairIso N)
        (tensorBridgeModel Z M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (tensorBridgeModel Z N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((kFlatQPair (Y := Z)).map g) _ (kFlatQPairIso_naturality g) ?_
      exact tensorBridgeModel_naturality Z g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] kFlatQPair_isLocalization

/-- **The two derived tensor products of this repository agree.**  The isomorphism of
bifunctors on `D(𝒪_Z) × D(𝒪_Z)`

`K ⊗^L_{𝒪_Z} L ≅ K ⊗^L_{𝒪_Z} L`

between the choice of Tag 06YU at which the monoidality of derived pullback is stated and the
choice at which the derived internal hom is stated.  On K-flat representatives both are the
total tensor complex, and `D(𝒪_Z) × D(𝒪_Z)` is the localization of the pairs of K-flat objects
of the homotopy category at the quasi-isomorphisms, which descends the identification. -/
def tensorBridge : pullbackTensorUncurried Z ≅ internalHomTensorUncurried Z :=
  Localization.liftNatIso (kFlatQPair (Y := Z)) (kFlatQuasiIsoPair (Y := Z)) _ _ _ _
    (tensorBridgeModels Z)

/-- **Tag 08DI with the derived tensor product written as a functor on pairs.**  The
tensor–internal-hom bijection on `D(𝒪_Z)`,

`Hom(A, R𝓗om(B, C)) ≃ Hom(A ⊗^L_{𝒪_Z} B, C)`,

at the uncurried spelling of the derived tensor product.  Fixing one spelling here is what
keeps every statement below a syntactic instance of the abstract transpose construction.

The bijection enters at the spelling Tag 08J8 is proved at, the site-level
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` of
`Stacks.SheafOfModules.ringedSite Z.sheaf`, rather than at the tagged Tag 08DI declaration
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`.  The latter is *defined* as the
former, so the two are the same family of additive equivalences and this is the same bijection;
but reading it off at `Z.sheaf` asks instance search for the additive structure of a hom group
of `D(𝒪_Z)` named through `Tensor.ringSheaf Z.sheaf`, which it cannot find, while at the site
the group is the one it already has. -/
def tensorHomEquiv
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) ≃
      ((internalHomTensorUncurried Z).obj (A, B) ⟶ C) :=
  (RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv

/-! ### Tag 079U at the derived tensor product of the internal hom -/

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- `Lh^*`, the derived pullback along a morphism of ringed spaces `h : X ⟶ Y`, as a functor
between the derived categories of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`. -/
abbrev derivedPullbackFunctor :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h

/-- **Tag 079U, at the derived tensor product the derived internal hom is stated at.**  For a
morphism of ringed spaces `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` the canonical isomorphism

`Lh^*(K ⊗^L_{𝒪_Y} L) ≅ Lh^*K ⊗^L_{𝒪_X} Lh^*L`,

bifunctorial in `K, L ∈ D(𝒪_Y)`.  It is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` conjugated by
`tensorBridge` on each side. -/
def pullbackTensorIso :
    internalHomTensorUncurried Y ⋙
        derivedPullbackFunctor h ≅
      (derivedPullbackFunctor h).prod
          (derivedPullbackFunctor h) ⋙
        internalHomTensorUncurried X :=
  Functor.isoWhiskerRight (tensorBridge Y).symm
      (derivedPullbackFunctor h) ≪≫
    derivedPullbackTensorIso h ≪≫
      Functor.isoWhiskerLeft
        ((derivedPullbackFunctor h).prod
          (derivedPullbackFunctor h))
        (tensorBridge X)

/-! ### The canonical map of Tag 08I3 -/

variable (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))

/-- **The derived evaluation** `R𝓗om_{𝒪_Y}(K, L) ⊗^L_{𝒪_Y} K ⟶ L`: the transpose of the
identity of `R𝓗om_{𝒪_Y}(K, L)` under the tensor–internal-hom bijection of Tag 08DI. -/
def derivedEvaluation :
    (internalHomTensorUncurried Y).obj
        ((((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L), K) ⟶ L :=
  Transpose.evaluation (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (internalHomTensorUncurried Y) (tensorHomEquiv Y) K L

/-- **The derived pullback of the evaluation**, read on the derived tensor product of the two
derived pullbacks: `Lh^*R𝓗om(K, L) ⊗^L_{𝒪_X} Lh^*K ⟶ Lh^*L`.  It is the monoidality
comparison of Tag 079U followed by the derived pullback of `derivedEvaluation`, and it is the
transpose datum the canonical map of Tag 08I3 is built from. -/
def derivedPullbackEvaluation :
    (internalHomTensorUncurried X).obj
        ((derivedPullbackFunctor h).obj
            (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L),
          (derivedPullbackFunctor h).obj K) ⟶
      (derivedPullbackFunctor h).obj L :=
  Transpose.homComparisonDatum
    (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X)
    (tensorHomEquiv Y) (pullbackTensorIso h) K L

/-- **Tag 08I3: the canonical map `Lh^*R𝓗om(K, L) ⟶ R𝓗om(Lh^*K, Lh^*L)`** for a morphism of
ringed spaces `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and objects `K, L` of `D(𝒪_Y)`.

By the tensor–internal-hom bijection of Tag 08DI it is the same datum as a map
`Lh^*R𝓗om(K,L) ⊗^L_{𝒪_X} Lh^*K ⟶ Lh^*L`, and that is the derived pullback of the evaluation
`R𝓗om(K,L) ⊗^L_{𝒪_Y} K ⟶ L` preceded by the monoidality comparison of Tag 079U. -/
@[stacks 08I3]
def derivedPullbackSheafHomMap :
    (derivedPullbackFunctor h).obj
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullbackFunctor h).obj K))).obj
        ((derivedPullbackFunctor h).obj L) :=
  Transpose.homComparison
    (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X)
    (tensorHomEquiv Y) (tensorHomEquiv X) (pullbackTensorIso h) K L

end

end Stacks.Cohomology.DerivedInternalHomPullback

end
