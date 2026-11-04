module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackModelAbstract

/-!
# The derived pullback of a derived internal Hom on algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `K, L ∈ D(𝒪_Y)`. This file constructs the
canonical map of [Stacks, Tag 08I3] for the small étale ringed topoi,

`Lf^*R𝓗om_{𝒪_Y}(K, L) ⟶ R𝓗om_{𝒪_X}(Lf^*K, Lf^*L)`,

and proves the formal properties it has for every `K`: it is natural in `K` and in `L`, it is the
component of a natural transformation of functors of `K`, and its invertibility passes to
retracts of `K`. The proof of [Stacks, Tag 0DKY] uses this map at the perfect approximations
`K_n` of a pseudo-coherent object, which is why naturality in `K` is the clause recorded here.

The construction is the source's, by
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`: by the tensor–internal-Hom
adjunction of Stacks 08J8 on `X`
(`AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction`) the map is the same datum as
a map `Lf^*R𝓗om(K, L) ⊗^L Lf^*K ⟶ Lf^*L`, and that is the derived pullback of the evaluation
`R𝓗om(K, L) ⊗^L K ⟶ L` preceded by the monoidality comparison of Stacks 07A4
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso`).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTensorHomEquiv`: the bijection
  `Hom(A, R𝓗om(P, C)) ≃ Hom(A ⊗^L P, C)` of Stacks 08J8 on an algebraic space.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap`: **the map of Stacks 08I3** for a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomNatTrans`: the same map as a natural
  transformation of functors of `K` on `D(𝒪_Y)ᵒᵖ`.

## Main results

* `AlgebraicGeometry.Space.tensorHomEquivNaturalLeft_smallEtale`,
  `AlgebraicGeometry.Space.tensorHomEquivDinatural_smallEtale` and
  `AlgebraicGeometry.Space.tensorHomEquivTargetNatural_smallEtale`: the three naturality clauses
  of Stacks 08J8 for that bijection.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap_naturality_source` and
  `smallEtaleDerivedPullbackSheafHomMap_naturality_target`: naturality in `K` and in `L`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_retract`: invertibility
  passes to a retract of `K`.

## Implementation notes

The derived internal Hom of an algebraic space and its adjunction are those of the equi-universe
model of the small étale ringed site, read through the derived equivalence with the model. The
dinaturality of the bijection in the internal-Hom variable is therefore the dinaturality on the
model, `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`, carried through the
equivalence by the abstract statement
`CategoryTheory.TransportedTensorHom.adjunction_homEquiv_symm_dinatural`, of which the adjunction
of an algebraic space is an instance by definition.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Bijection

variable (X : AlgebraicSpaces B S hS)

/-- **The bijection of Stacks 08J8 on an algebraic space**: `Hom(A, R𝓗om(P, C)) ≃ Hom(A ⊗^L P, C)`,
the inverse of the bijection of the adjunction `- ⊗^L P ⊣ R𝓗om(P, -)`. -/
def smallEtaleTensorHomEquiv
    (A P C : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (A ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj C) ≃
      ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)).obj (A, P) ⟶ C) :=
  ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv A C).symm

/-- **Stacks 08J8 on an algebraic space, in the source variable**: the transpose of `φ ≫ ψ` is the
transpose of `ψ` precomposed with `φ ⊗ 1`. -/
theorem tensorHomEquivNaturalLeft_smallEtale :
    Transpose.TensorHomEquivNaturalLeft (smallEtaleDerivedSheafHom B S hS X)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleTensorHomEquiv B S hS X) := by
  intro A A' P C φ ψ
  rw [EquivalenceTranspose.uncurryObj_map_mkHom_id]
  exact (smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv_naturality_left_symm φ ψ

/-- **Stacks 08J8 on an algebraic space, in the target variable**: the transpose of
`ψ ≫ R𝓗om(P, φ)` is the transpose of `ψ` followed by `φ`. -/
theorem tensorHomEquivTargetNatural_smallEtale :
    EquivalenceTranspose.CurriedTargetNatural (smallEtaleDerivedSheafHom B S hS X)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleTensorHomEquiv B S hS X) :=
  fun A P _ _ φ ψ =>
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv_naturality_right_symm ψ φ

/-- **Stacks 08J8 on an algebraic space, in the internal-Hom variable**: for `φ : P' ⟶ P`, the
transpose of `ψ ≫ R𝓗om(φ, C)` is the transpose of `ψ` precomposed with `1 ⊗ φ`. -/
theorem tensorHomEquivDinatural_smallEtale :
    Transpose.TensorHomEquivDinatural (smallEtaleDerivedSheafHom B S hS X)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleTensorHomEquiv B S hS X) := by
  intro A P P' C φ ψ
  rw [uncurry_map_id_mkHom]
  exact smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS X A C φ ψ

end Bijection

section Map

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Stacks 08I3 for a morphism of algebraic spaces**: the canonical map

`Lf^*R𝓗om_{𝒪_Y}(K, L) ⟶ R𝓗om_{𝒪_X}(Lf^*K, Lf^*L)`.

By the bijection of Stacks 08J8 on `X` it is the same datum as a map
`Lf^*R𝓗om(K, L) ⊗^L Lf^*K ⟶ Lf^*L`, and that is the derived pullback of the evaluation
`R𝓗om(K, L) ⊗^L K ⟶ L` preceded by the monoidality comparison of Stacks 07A4. -/
def smallEtaleDerivedPullbackSheafHomMap
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullback B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op K)).obj L) ⟶
      ((smallEtaleDerivedSheafHom B S hS X).obj
          (op ((smallEtaleDerivedModulePullback B S hS f).obj K))).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj L) :=
  Transpose.homComparison (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f) K L

/-- **The transpose of the map of Stacks 08I3** under the bijection of Stacks 08J8 on `X` is the
comparison of Stacks 07A4 followed by the derived pullback of the evaluation. -/
theorem smallEtaleTensorHomEquiv_smallEtaleDerivedPullbackSheafHomMap
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    smallEtaleTensorHomEquiv B S hS X _ _ _ (smallEtaleDerivedPullbackSheafHomMap f K L) =
      (smallEtaleDerivedPullbackTensorIso f).inv.app
          (((smallEtaleDerivedSheafHom B S hS Y).obj (op K)).obj L, K) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          (smallEtaleTensorHomEquiv B S hS Y _ _ _ (𝟙 _)) :=
  Transpose.homComparison_adjoint (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f) K L

/-- **The map of Stacks 08I3 is natural in its first variable**: for `φ : K ⟶ K'`,
`Lf^*R𝓗om(φ, L)` followed by the map at `K` is the map at `K'` followed by
`R𝓗om(Lf^*φ, Lf^*L)`. -/
theorem smallEtaleDerivedPullbackSheafHomMap_naturality_source
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (φ : K ⟶ K')
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullback B S hS f).map
        (((smallEtaleDerivedSheafHom B S hS Y).map φ.op).app L) ≫
      smallEtaleDerivedPullbackSheafHomMap f K L =
    smallEtaleDerivedPullbackSheafHomMap f K' L ≫
      ((smallEtaleDerivedSheafHom B S hS X).map
        ((smallEtaleDerivedModulePullback B S hS f).map φ).op).app
          ((smallEtaleDerivedModulePullback B S hS f).obj L) :=
  Transpose.homComparison_naturality_source (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y) (tensorHomEquivDinatural_smallEtale B S hS Y)
    (tensorHomEquivNaturalLeft_smallEtale B S hS X) (tensorHomEquivDinatural_smallEtale B S hS X)
    φ L

/-- **The map of Stacks 08I3 is natural in its second variable.** -/
theorem smallEtaleDerivedPullbackSheafHomMap_naturality_target
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    {L L' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (k : L ⟶ L') :
    (smallEtaleDerivedModulePullback B S hS f).map
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op K)).map k) ≫
      smallEtaleDerivedPullbackSheafHomMap f K L' =
    smallEtaleDerivedPullbackSheafHomMap f K L ≫
      ((smallEtaleDerivedSheafHom B S hS X).obj
        (op ((smallEtaleDerivedModulePullback B S hS f).obj K))).map
          ((smallEtaleDerivedModulePullback B S hS f).map k) :=
  Transpose.homComparison_naturality_target (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y)
    (tensorHomEquivTargetNatural_smallEtale B S hS Y)
    (tensorHomEquivNaturalLeft_smallEtale B S hS X)
    (tensorHomEquivTargetNatural_smallEtale B S hS X)
    K k

/-- **The map of Stacks 08I3 as a natural transformation of its first variable**, from
`K ↦ Lf^*R𝓗om(K, L)` to `K ↦ R𝓗om(Lf^*K, Lf^*L)` on `D(𝒪_Y)ᵒᵖ`. Its components are
`smallEtaleDerivedPullbackSheafHomMap`, by `rfl`. -/
abbrev smallEtaleDerivedPullbackSheafHomNatTrans
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    Transpose.comparisonSourceFunctor (smallEtaleDerivedModulePullback B S hS f)
        (smallEtaleDerivedSheafHom B S hS Y) L ⟶
      Transpose.comparisonTargetFunctor (smallEtaleDerivedModulePullback B S hS f)
        (smallEtaleDerivedSheafHom B S hS X) L :=
  Transpose.homComparisonNatTrans (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y) (tensorHomEquivDinatural_smallEtale B S hS Y)
    (tensorHomEquivNaturalLeft_smallEtale B S hS X) (tensorHomEquivDinatural_smallEtale B S hS X) L

/-- **Invertibility of the map of Stacks 08I3 passes to a retract of the first variable.** If
`K ⟶ K' ⟶ K` is the identity and the map is invertible at `K'`, it is invertible at `K`. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_retract
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (i : K ⟶ K') (r : K' ⟶ K) (hir : i ≫ r = 𝟙 K)
    (hK' : IsIso (smallEtaleDerivedPullbackSheafHomMap f K' L)) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L) :=
  Transpose.isIso_homComparison_of_retract (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Y) (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso f)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y) (tensorHomEquivDinatural_smallEtale B S hS Y)
    (tensorHomEquivNaturalLeft_smallEtale B S hS X) (tensorHomEquivDinatural_smallEtale B S hS X)
    L i r hir hK'

end Map

end AlgebraicGeometry.Space

end
