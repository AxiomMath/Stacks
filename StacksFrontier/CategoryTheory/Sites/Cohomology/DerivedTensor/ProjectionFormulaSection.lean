module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfectOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula of a morphism of ringed topoi, as a transformation of bifunctors

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi.  Section 21.50 of
[Stacks, Tag 0943] produces, for `E ∈ D(𝒪_𝒞)` and `K ∈ D(𝒪_𝒟)` and with no further hypothesis,
a canonical map

`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`,

adjoint for `Lf^* ⊣ Rf_*` to `Lf^*(Rf_*E ⊗^𝐋 K) ≅ Lf^*Rf_*E ⊗^𝐋 Lf^*K ⟶ E ⊗^𝐋 Lf^*K`, and
asserts that it is an isomorphism when `K` is perfect.

Both sides of the map are functors of the *pair* `(E, K)`, and the source says that the map is
canonical, i.e. natural in `E` and `K` together.  This file states that: the map is assembled
into a single morphism of bifunctors on `D(𝒪_𝒞) × D(𝒪_𝒟)`, and the lemma of the section is
read on it as the invertibility, for perfect `K`, of the whole natural transformation in `E`
rather than of its value at one `E` at a time.

## Main definitions

All in the namespace `Stacks.Cohomology.ProjectionFormulaSection`.

* `pushforwardTensor` — the bifunctor `(E, K) ↦ Rf_*E ⊗^𝐋_{𝒪_𝒟} K`, the source of the map.
* `tensorPullbackPushforward` — the bifunctor `(E, K) ↦ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`, its target.
* `projectionFormula` — **the canonical map of Section 21.50**, as a morphism of those two
  bifunctors.
* `projectionFormulaNatTransSource` — its restriction to a fixed `K`, as a natural
  transformation of functors of `E`.

## Main results

* `isIso_projectionFormulaNatTransSource` — **the lemma of Section 21.50**: for perfect `K` the
  natural transformation of functors of `E` is invertible, so that
  `Rf_*(-) ⊗^𝐋_{𝒪_𝒟} K ≅ Rf_*(- ⊗^𝐋_{𝒪_𝒞} Lf^*K)` as functors `D(𝒪_𝒞) ⥤ D(𝒪_𝒟)`.

## Implementation notes

*What is new here and what is reused.*  The map itself and its two separate naturality clauses
are `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap` and its companions,
and the invertibility at a perfect complex is
`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isPerfect`; this
file adds the functorial packaging the section's word "canonical" asserts.  The joint naturality
in the two variables is one application of `CategoryTheory.adjunctionTensorMap_natural`, the
naturality of the abstract adjoint-transpose construction the map is an instance of, so no new
coherence of the comparison of [Stacks, Tag 07A4] is needed; the one-variable natural
transformation `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaNatTrans` is in
the other variable — `E` fixed, `K` varying — and is used by the dévissage of
[Stacks, Tag 0944], whereas the invertibility statement of the section fixes `K`, the perfect
complex, and lets `E` vary.

*The order of the tensor factors.*  The two bifunctors are the derived tensor products of
[Stacks, Tag 06YU] with their arguments in the given order, so the map comes out with the
factors as the source writes them and no symmetry of `⊗^𝐋` enters.

*Universes and instances.*  The ringed topoi are `AlgebraicGeometry.RingedTopos.{u, u, u}`, the
generality in which the derived pullback, the derived pushforward and the derived tensor product
of a morphism of ringed topoi are available; the sheafification and composition properties these
carry hold for every such ringed topos and are supplied by instance search, exactly as in
`ProjectionFormulaPerfectOfToposHom`.

## References

* [Stacks Project, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaSection

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- **The source of the projection formula map**, as a bifunctor: the derived pushforward in the
first variable followed by the derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_𝒟)`,
`(E, K) ↦ Rf_*E ⊗^𝐋_{𝒪_𝒟} K`. -/
def pushforwardTensor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.prod (derivedPushforward (X := X) (Y := Y) f)
      (𝟭 (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ⋙
    Functor.uncurry.obj (derivedTensorProductFunctor Y.O)

/-- **The target of the projection formula map**, as a bifunctor: the derived pullback in the
second variable, then the derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_𝒞)`, then the
derived pushforward, `(E, K) ↦ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`. -/
def tensorPullbackPushforward :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.prod
      (𝟭 (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (derivedPullback f : DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
    Functor.uncurry.obj (derivedTensorProductFunctor X.O) ⋙
      derivedPushforward (X := X) (Y := Y) f

/-- **The canonical map of Section 21.50 of [Stacks, Tag 0943]**, as a morphism of bifunctors on
`D(𝒪_𝒞) × D(𝒪_𝒟)`:

`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`,

natural in `E` and `K` together.  Its value at a pair is the map of [Stacks, Tag 0B56], the
adjoint for `Lf^* ⊣ Rf_*` of the comparison `Lf^*(Rf_*E ⊗^𝐋 K) ≅ Lf^*Rf_*E ⊗^𝐋 Lf^*K` of
[Stacks, Tag 07A4] followed by the counit `Lf^*Rf_*E ⟶ E` in the first factor.  There is no
hypothesis on `f`, `E` or `K`: the section stresses that the map exists for every morphism of
ringed topoi, and the joint naturality is the naturality of the adjoint-transpose construction
the map instantiates. -/
@[stacks 0943 "the canonical map of Section 21.50, natural in the two complexes together"]
def projectionFormula : pushforwardTensor f ⟶ tensorPullbackPushforward f where
  app P := projectionFormulaMap f P.1 P.2
  naturality _ _ g := by
    have h := CategoryTheory.adjunctionTensorMap_natural (derivedAdjunction f)
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom g.1 g.2
    simpa [pushforwardTensor, tensorPullbackPushforward, projectionFormulaMap] using h

/-- The component of `projectionFormula f` at a pair `(E, K)` is `projectionFormulaMap f E K`. -/
@[simp]
lemma projectionFormula_app
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (projectionFormula f).app (E, K) = projectionFormulaMap f E K :=
  rfl

/-- **The canonical map of Section 21.50 at a fixed complex `K` on the target**, as a natural
transformation of functors of the complex on the source:

`Rf_*(-) ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(- ⊗^𝐋_{𝒪_𝒞} Lf^*K)`.

This is the shape in which the lemma of the section is an isomorphism of functors: there `K` is
the perfect complex and `E` ranges over `D(𝒪_𝒞)`. -/
def projectionFormulaNatTransSource
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    derivedPushforward (X := X) (Y := Y) f ⋙
        Stacks.ProjectionFormula.tensorRightOf
          (Functor.uncurry.obj (derivedTensorProductFunctor Y.O)) K ⟶
      Stacks.ProjectionFormula.tensorRightOf
          (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
          ((derivedPullback f).obj K) ⋙
        derivedPushforward (X := X) (Y := Y) f where
  app E := projectionFormulaMap f E K
  naturality _ _ φ := by
    have h := CategoryTheory.adjunctionTensorMap_natural (derivedAdjunction f)
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom φ (𝟙 K)
    simpa [Stacks.ProjectionFormula.tensorRightOf, projectionFormulaMap] using h

/-- The component of `projectionFormulaNatTransSource f K` at `E` is
`projectionFormulaMap f E K`. -/
@[simp]
lemma projectionFormulaNatTransSource_app
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (projectionFormulaNatTransSource f K).app E = projectionFormulaMap f E K :=
  rfl

/-- **The lemma of Section 21.50 of [Stacks, Tag 0943]**, as an isomorphism of functors.  Let
`f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi and let `K ∈ D(𝒪_𝒟)` be
perfect.  Then the canonical map of the section is invertible as a natural transformation of
functors of the complex on the source:

`Rf_*(-) ⊗^𝐋_{𝒪_𝒟} K ≅ Rf_*(- ⊗^𝐋_{𝒪_𝒞} Lf^*K)` on `D(𝒪_𝒞) ⥤ D(𝒪_𝒟)`.

A natural transformation is invertible as soon as each of its components is, and each component
is [Stacks, Tag 0944]. -/
@[stacks 0943 "the lemma of Section 21.50: at a perfect complex the canonical map is invertible, \
here as an isomorphism of the two functors of the complex on the source"]
theorem isIso_projectionFormulaNatTransSource
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : RingedSite.IsPerfect Y.toRingedSite K) :
    IsIso (projectionFormulaNatTransSource f K) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (projectionFormulaNatTransSource f K) fun E => by
    rw [projectionFormulaNatTransSource_app]
    exact isIso_projectionFormulaMap_of_isPerfect f E K hK

end Stacks.Cohomology.ProjectionFormulaSection

end
