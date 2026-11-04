module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import Mathlib.AlgebraicGeometry.Scheme
import StacksCore.Tactic.StacksAttribute

/-!
# Derived Hom into a fixed complex, and the canonical biduality morphism

Let `(X, 𝒪_X)` be a ringed space and `K` an object of `D(𝒪_X)`. This file constructs the
contravariant functor

`D = R𝓗om_{𝒪_X}(-, K) : D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)`

out of the derived internal Hom bifunctor of [Stacks, Tag 08DH]
(`Stacks.SheafOfModules.derivedSheafHom`), and the canonical **biduality** morphism

`L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`,

natural in `L`, as a natural transformation `𝟭 ⟶ opOp ⋙ D.op ⋙ D` on the whole of `D(𝒪_X)`.
Both are then read at a scheme, where they are the functor `D` and the canonical morphism
`id → D ∘ D` of [Stacks, Tag 0A89].

## The construction

The biduality morphism is the three-step composite that
`Stacks.SheafOfModules.derivedBidualMap` uses at `K = 𝒪_X`, with the trivialisation
`𝒪_X ≅ R𝓗om_{𝒪_X}(𝒪_X, 𝒪_X)` replaced by the homothety of a general `K`:

* the left unitor read backwards, `L ≅ 𝒪_X[0] ⊗^𝐋_{𝒪_X} L`, for the monoidal structure
  `Stacks.SheafOfModules.derivedMonoidalStructure` of [Stacks, Tag 0FPT], whose tensor product
  *is* `Stacks.SheafOfModules.derivedTensor` and whose unit *is* the structure sheaf in degree
  zero, both by `rfl`;
* the homothety `Stacks.SheafOfModules.derivedSheafHomothety` of `K`, whiskered on the right by
  `L`, giving `𝒪_X[0] ⊗^𝐋_{𝒪_X} L ⟶ R𝓗om_{𝒪_X}(K, K) ⊗^𝐋_{𝒪_X} L`;
* the derived evaluation morphism of [Stacks, Tag 0A8U],
  `Stacks.SheafOfModules.derivedSheafHomEvaluation` at `(L, K, K)`, whose target is literally
  `R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`.

Naturality needs nothing beyond naturality of the left unitor, the whiskering interchange law,
and `Stacks.SheafOfModules.derivedSheafHomEvaluation_natural`, the functoriality of derived
evaluation in all three objects at once of [Stacks, Tag 0A8U], read at `(f, 𝟙 K, 𝟙 K)`.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomInto` — `R𝓗om_{𝒪_X}(-, K)` as a functor
  `D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)`.
* `Stacks.SheafOfModules.derivedSheafHomBidualMap` — the canonical biduality morphism at an
  object.
* `Stacks.SheafOfModules.derivedSheafHomBidual` — the same, as a natural transformation
  `𝟭 ⟶ opOp ⋙ D.op ⋙ D`.
* `Stacks.Duality.dualizingDerivedSheafHomFunctor` — **[Stacks, Tag 0A89]**, the functor
  `D = R𝓗om_{𝒪_X}(-, K)` on a scheme.
* `Stacks.Duality.dualizingDerivedSheafHomBiduality` — **[Stacks, Tag 0A89]**, the canonical
  morphism `id → D ∘ D` on a scheme.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomBidualMap_naturality` — the biduality morphism is
  natural in its object.

## Where the rest of Tag 0A89 lives

[Stacks, Tag 0A89] has several separable assertions about a dualizing complex `K` on a locally
Noetherian scheme `X`. This file supplies the functor `D` and the canonical morphism
`id → D ∘ D`, both for an arbitrary `K`. The others:

* that `K` lies in `D_Coh(𝒪_X)` is
  `Stacks.Duality.mem_coherentDerivedCategory_of_isDualizingComplex`;
* that `D` carries `D_Coh(𝒪_X)` into `D_Coh(𝒪_X)` is
  `Stacks.Duality.derivedCategoryB_isCoherent_dualizingDerivedSheafHom` of
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityCoherence.lean`;
* the exchange of `D⁺_Coh(𝒪_X)` and `D⁻_Coh(𝒪_X)` for quasi-compact `X`, and that `D^b_Coh(𝒪_X)`
  is preserved, are the three results of
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityBounded.lean`;
* that the canonical morphism `id → D ∘ D` below is an **isomorphism** at every object of
  `D_Coh(𝒪_X)`, and the two anti-equivalences that follow from it, are
  `Stacks.Duality.isIso_dualizingDerivedSheafHomBiduality_app`,
  `Stacks.Duality.coherentDualizingDerivedSheafHom_isEquivalence` and
  `Stacks.Duality.boundedCoherentDualizingDerivedSheafHom_isEquivalence` of
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityBiduality.lean`.

The morphism below is the left unitor, the homothety of `K` and the derived evaluation morphism
of [Stacks, Tag 0A8U], so invertibility of the last two is its whole content. The homothety of a
dualizing complex is invertible by
`Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`, and the evaluation morphism
at a source with coherent cohomology sheaves by
`Stacks.Duality.isIso_derivedSheafHomEvaluation_of_isDualizingComplex`. Neither goes through
[Stacks, Tag 0A88] in the shape the source uses, which would ask for the comparison morphism
`(R Hom_A(K, L))~ ⟶ R𝓗om_{𝒪_{Spec A}}(K̃, L̃)` to be identified with an evaluation morphism —
an identification the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineDualizingHomothety.lean` records as
unavailable, the comparison being natural in both variables with nothing linking it to an
evaluation morphism. Nor does either go through clause (2) of [Stacks, Tag 0G4I],
`Stacks.SheafOfModules.derivedSheafHomEvaluation_isIso_of_coherent_finiteTorDimension`, which
asks for
`Stacks.SheafOfModules.HoldsAffineLocally X (HasFiniteInjectiveDimensionOverOpen X K)` — finite
injective dimension of `K` restricted to an affine open **as a complex of `𝒪_X|_U`-modules**.
The implementation notes of
`StacksFrontier/AlgebraicGeometry/InternalHomEvaluation/CoherentEvaluation.lean` record that the
passage to it from finite injective dimension over `Γ(X, U)` — the condition a dualizing complex
satisfies, by `Dualizing.IsDualizingComplex.finiteInjectiveDimension` — is the statement that
`Ĩ` is an injective `𝒪_U`-module for an injective module `I` over a Noetherian ring, which the
library does not have and which the proof of Tag 0A88 deliberately avoids
([Stacks, Tag 0CRZ]). Instead the dévissage of [Stacks, Tag 0A69] is run directly on sheaves, so
that the amplitude bounds of Tag 0A88 are applied over `Spec Γ(X, U)` and never asked of
`𝒪_X|_U` itself; that is
`StacksFrontier/AlgebraicGeometry/InternalHomEvaluation/DualizingEvaluation.lean`.

## Implementation notes

The ringed-space half is stated for an arbitrary `K`, with no hypothesis: the functor and the
biduality morphism exist for every object of `D(𝒪_X)`, and a dualizing complex enters only in
the assertions this file does not prove. This matches
`Stacks.SheafOfModules.derivedBidualMap`, and on the affine side
`Dualizing.dualizingDerivedHomFunctor` and `Dualizing.derivedBiduality`, which carry the
`@[stacks 0A7C]` attributes of the corresponding fragments of the affine statement at an
arbitrary `ω` as well.

The derived category is the standard model, `CategoryTheory.HasDerivedCategory.standard`: it is
the model `Stacks.SheafOfModules.derivedSheafHom`,
`Stacks.SheafOfModules.derivedSheafHomothety` and
`Stacks.SheafOfModules.derivedSheafHomEvaluation` are stated at, so the choice is forced rather
than made. It differs from the free `[HasDerivedCategory.{w} X.Modules]` binder of
`Stacks.Duality.mem_coherentDerivedCategory_of_isDualizingComplex`; the standard model is a
legitimate derived category of `X.Modules`, no statement below mentions coproducts, and the
import surface is kept narrow so that the *global* locally small instance of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` does not displace the choice, exactly
as in `StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineCoherentDerivedHom.lean`.

`AlgebraicGeometry.Scheme.Modules X` and `Stacks.SheafOfModules.StructureSheafModules X.sheaf`
are the same category by `rfl`, which is what lets the scheme-level declarations be the
ringed-space ones read at `X.sheaf`. The two additivity facts and the total-complex instance
that the derived internal Hom of a ringed space is stated with are scoped instances and are
named for local instance search, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineCoherentDerivedHom.lean`.

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0G4I](https://stacks.math.columbia.edu/tag/0G4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-- `R𝓗om_{𝒪_X}(-, K)`, derived internal Hom into a fixed object `K` of `D(𝒪_X)`, as a
contravariant functor `D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)`: the derived internal Hom bifunctor of
[Stacks, Tag 08DH] with its second argument frozen at `K`. -/
abbrev derivedSheafHomInto (K : DerivedCategory (StructureSheafModules Rc)) :
    (DerivedCategory (StructureSheafModules Rc))ᵒᵖ ⥤
      DerivedCategory (StructureSheafModules Rc) :=
  (derivedSheafHom Rc).flip.obj K

/-- **The canonical biduality morphism** `L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`, for arbitrary
objects `K`, `L` of `D(𝒪_X)` on a ringed space.

It is the left unitor read backwards, the homothety
`Stacks.SheafOfModules.derivedSheafHomothety` of `K` whiskered by `L`, and the derived
evaluation morphism of [Stacks, Tag 0A8U] at `(L, K, K)`, in that order. No hypothesis on either
object is needed to define it. -/
def derivedSheafHomBidualMap (K L : DerivedCategory (StructureSheafModules Rc)) :
    L ⟶ (derivedSheafHomInto Rc K).obj (op ((derivedSheafHomInto Rc K).obj (op L))) :=
  (λ_ L).inv ≫ (derivedSheafHomothety Rc K ▷ L) ≫ derivedSheafHomEvaluation Rc L K K

/-- The biduality morphism is the left unitor, the homothety of `K` and the derived evaluation
morphism of [Stacks, Tag 0A8U], in that order. This pins it down and is the form in which to
rewrite it. -/
theorem derivedSheafHomBidualMap_eq (K L : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomBidualMap Rc K L =
      (λ_ L).inv ≫ (derivedSheafHomothety Rc K ▷ L) ≫ derivedSheafHomEvaluation Rc L K K :=
  rfl

/-- **The canonical biduality morphism is natural in its object.** The left unitor is natural,
whiskering on the left and on the right commute, and derived evaluation is functorial in all
three of its objects ([Stacks, Tag 0A8U]); read at `(f, 𝟙 K, 𝟙 K)` those three facts are the
naturality square. -/
theorem derivedSheafHomBidualMap_naturality
    (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (f : L ⟶ L') :
    f ≫ derivedSheafHomBidualMap Rc K L' =
      derivedSheafHomBidualMap Rc K L ≫
        (derivedSheafHomInto Rc K).map (((derivedSheafHomInto Rc K).map f.op).op) := by
  have h₁ : derivedSheafHomMap Rc (𝟙 K) (𝟙 K) = 𝟙 (((derivedSheafHom Rc).obj (op K)).obj K) :=
    RingedSite.derivedSheafHomMap_id (ringedSite Rc) (derivedInternalHom Rc) K K
  have h₂ : derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op K)).obj K)) f =
      ((derivedSheafHom Rc).obj (op K)).obj K ◁ f :=
    RingedSite.derivedTensorMap_id_left (ringedSite Rc)
      (canonicalDerivedTensorProduct (ringedSite Rc)) _ f
  have h₃ : ∀ {A B : DerivedCategory (StructureSheafModules Rc)} (a : A ⟶ B),
      derivedSheafHomMap Rc a (𝟙 K) = (derivedSheafHomInto Rc K).map a.op := fun a =>
    RingedSite.derivedSheafHomMap_id_right (ringedSite Rc) (derivedInternalHom Rc) a K
  have hev := derivedSheafHomEvaluation_natural Rc f (𝟙 K) (𝟙 K)
  rw [h₁, h₂, h₃, h₃] at hev
  dsimp only [derivedSheafHomBidualMap]
  rw [← Category.assoc, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙_ (DerivedCategory (StructureSheafModules Rc)) ◁ f),
    whisker_exchange, Category.assoc, hev]

/-- **The canonical biduality morphisms, natural in the object**: the natural transformation
`𝟭 ⟶ opOp ⋙ D.op ⋙ D` on `D(𝒪_X)`, where `D = R𝓗om_{𝒪_X}(-, K)`. Its components are
`Stacks.SheafOfModules.derivedSheafHomBidualMap` and its naturality is
`Stacks.SheafOfModules.derivedSheafHomBidualMap_naturality`. -/
def derivedSheafHomBidual (K : DerivedCategory (StructureSheafModules Rc)) :
    Functor.id (DerivedCategory (StructureSheafModules Rc)) ⟶
      opOp (DerivedCategory (StructureSheafModules Rc)) ⋙
        (derivedSheafHomInto Rc K).op ⋙ derivedSheafHomInto Rc K where
  app L := derivedSheafHomBidualMap Rc K L
  naturality {_L _L'} f := derivedSheafHomBidualMap_naturality Rc K f

/-- The components of `Stacks.SheafOfModules.derivedSheafHomBidual` are the canonical biduality
morphisms. -/
@[simp]
theorem derivedSheafHomBidual_app (K L : DerivedCategory (StructureSheafModules Rc)) :
    (derivedSheafHomBidual Rc K).app L = derivedSheafHomBidualMap Rc K L :=
  rfl

end Stacks.SheafOfModules

namespace Stacks.Duality

open Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable (X : Scheme.{u}) (K : DerivedCategory X.Modules)

/-- **Stacks Project, Tag 0A89.** The functor `D = R𝓗om_{𝒪_X}(-, K)` of the lemma: derived
internal Hom into `K` as a contravariant functor `D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)` on a scheme.

As on the affine side (`Dualizing.dualizingDerivedHomFunctor`, which carries the corresponding
fragment of [Stacks, Tag 0A7C]) it is defined for an arbitrary `K`; that `K` be a dualizing
complex is what makes `D` an anti-equivalence of `D_Coh(𝒪_X)`, a separate assertion of the tag,
which is `Stacks.Duality.coherentDualizingDerivedSheafHom_isEquivalence` — see the section
"Where the rest of Tag 0A89 lives" above. -/
@[stacks 0A89 "the functor D = R SheafHom(-, K) on D(O_X)", sga "5 III 6.2" "partial"]
def dualizingDerivedSheafHomFunctor :
    (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules :=
  derivedSheafHomInto X.sheaf K

/-- The functor `D = R𝓗om_{𝒪_X}(-, K)` sends `L` to `R𝓗om_{𝒪_X}(L, K)`. -/
@[simp]
theorem dualizingDerivedSheafHomFunctor_obj (L : DerivedCategory X.Modules) :
    (dualizingDerivedSheafHomFunctor X K).obj (op L) =
      ((derivedSheafHom X.sheaf).obj (op L)).obj K :=
  rfl

/-- **Stacks Project, Tag 0A89.** The canonical morphism `id → D ∘ D` of the lemma, for
`D = R𝓗om_{𝒪_X}(-, K)` on a scheme: the natural transformation
`𝟭 ⟶ opOp ⋙ D.op ⋙ D` whose component at `L` is the biduality morphism

`L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`

of `Stacks.SheafOfModules.derivedSheafHomBidualMap`.

Here the morphism is constructed, for an arbitrary `K`, exactly as `Dualizing.derivedBiduality`
constructs the affine one; that it is an isomorphism at every object of `D_Coh(𝒪_X)` is
`Stacks.Duality.isIso_dualizingDerivedSheafHomBiduality_app`, the counterpart of
`Dualizing.dualizingDerivedHom_biduality_isIso`. -/
@[stacks 0A89 "the canonical biduality morphism id → D ∘ D"]
def dualizingDerivedSheafHomBiduality :
    Functor.id (DerivedCategory X.Modules) ⟶
      opOp (DerivedCategory X.Modules) ⋙ (dualizingDerivedSheafHomFunctor X K).op ⋙
        dualizingDerivedSheafHomFunctor X K :=
  derivedSheafHomBidual X.sheaf K

/-- The components of `Stacks.Duality.dualizingDerivedSheafHomBiduality` are the canonical
biduality morphisms of `Stacks.SheafOfModules.derivedSheafHomBidualMap`. -/
@[simp]
theorem dualizingDerivedSheafHomBiduality_app (L : DerivedCategory X.Modules) :
    (dualizingDerivedSheafHomBiduality X K).app L = derivedSheafHomBidualMap X.sheaf K L :=
  rfl

end Stacks.Duality

end
