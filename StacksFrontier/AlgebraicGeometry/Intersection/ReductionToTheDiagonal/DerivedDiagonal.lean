module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSiteTensorHomAdjunction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to the diagonal in the derived category

Let `f : X ⟶ S` be a morphism of schemes, `pr₁, pr₂ : X ×_S X ⟶ X` the two projections and
`Δ : X ⟶ X ×_S X` the diagonal. This file proves part (2) of [Stacks, Tag 0B0T]: for `K` and
`M` in `D(𝒪_X)` there are canonical isomorphisms

* `LΔ^*(Lpr₁^*K ⊗^L Lpr₂^*M) ≅ K ⊗^L M`, and
* `𝒪_Δ ⊗^L (Lpr₁^*K ⊗^L Lpr₂^*M) ≅ Δ_*(K ⊗^L M)` when `f` is separated,

both natural in the pair `(K, M)`.

## Main definitions

* `Stacks.Intersection.Diagonal.derivedRestrictionIso`: for a morphism of ringed spaces
  `δ : X ⟶ P` with two retractions `p₁, p₂`, the isomorphism of bifunctors
  `Lδ^*(Lp₁^*K ⊗^L Lp₂^*M) ≅ K ⊗^L M`.
* `Stacks.Intersection.Diagonal.diagonalRestrictionIso`: its value at the diagonal.
* `Stacks.Intersection.Diagonal.diagonalStructureModule`: `𝒪_Δ = Δ_*𝒪_X`.
* `Stacks.Intersection.Diagonal.diagonalTensorIso`: the second isomorphism.
* `Stacks.Intersection.Diagonal.derivedDiagonalIsos`: **[Stacks, Tag 0B0T] part (2)**, the two
  isomorphisms together.

## Main results

* `Stacks.Intersection.Diagonal.derivedRestrictionIso_hom` and
  `Stacks.Intersection.Diagonal.diagonalTensorIso_hom`: the defining formulas, which pin the two
  isomorphisms down as composites of canonical maps.

## Implementation notes

The source's proof is followed. The first isomorphism is the comparison of [Stacks, Tag 079U]
for `Δ` (`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`), followed in each
factor by `LΔ^*Lprᵢ^* ≅ L(prᵢ ∘ Δ)^* = L(𝟙)^* ≅ 𝟭` ([Stacks, Tag 0D5S],
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, and
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso`). The source represents `K` and
`M` by K-flat complexes and identifies `Δ^*(pr₁^*K ⊗ pr₂^*M)` with `K ⊗ M` termwise; that
termwise identification is exactly what the composite of the comparisons of Tag 079U and Tag 0D5S
is on K-flat representatives, so nothing is lost by working with the derived functors directly.

The second isomorphism is the projection formula for the closed immersion `Δ`, read at the
structure sheaf: `Δ_*𝒪_X ⊗^L E ≅ Δ_*LΔ^*E`, which is
`Stacks.Duality.TensorHomTorAmplitude.tensorPushforwardStructureSheafNatIso` ([Stacks, Tag 0B55]
with the unit constraint of [Stacks, Tag 0FPT]), followed by `Δ_*` of the first isomorphism.
Since `Δ` is a closed immersion its direct image is exact, and `Δ_*` on derived categories is the
functor induced by the exact functor `Δ_*` (this is `RΔ_*`, by [Stacks, Tag 0E2K]).

*Hypotheses.* The source states the lemma for a nonsingular variety `X` and `K, M ∈ D_QCoh(𝒪_X)`.
Nothing of that is used: the first isomorphism exists for every morphism of schemes `f : X ⟶ S`
and all `K, M ∈ D(𝒪_X)`, and the second needs only that `Δ` be a closed immersion, i.e. that `f`
be separated, which a variety is. As `D_QCoh(𝒪_X)` is a full subcategory of `D(𝒪_X)`, the
isomorphisms restrict to isomorphisms in `D_QCoh`.

Everything is at the model `CategoryTheory.HasDerivedCategory.standard` of the derived categories,
which is the model at which [Stacks, Tag 079U] and [Stacks, Tag 0B55] are stated; its priority is
raised so that the locally small model arriving with the imports does not compete.

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Intersection.Diagonal

attribute [local instance 10000] HasDerivedCategory.standard

section RingedSpace

variable {X P : RingedSpace.{u, u}} (δ : X ⟶ P)

/-- For a section `δ` of `p` (that is `δ ≫ p = 𝟙 X`), the composite `Lδ^* ∘ Lp^*` is the identity:
the composition comparison `Lp^* ⋙ Lδ^* ≅ L(δ ≫ p)^*` of [Stacks, Tag 0D5S] followed by
`L(𝟙 X)^* ≅ 𝟭`. -/
def derivedPullbackRetractionIso (p : P ⟶ X) (h : δ ≫ p = 𝟙 X) :
    derivedPullback p ⋙ derivedPullback δ ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical δ p ≪≫
    eqToIso (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq h) ≪≫
    Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X

variable (p₁ p₂ : P ⟶ X) (h₁ : δ ≫ p₁ = 𝟙 X) (h₂ : δ ≫ p₂ = 𝟙 X)

/-- The exterior derived tensor product `(K, M) ↦ Lp₁^*K ⊗^L Lp₂^*M`. -/
abbrev exteriorDerivedTensor :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing P)) :=
  (derivedPullback p₁).prod (derivedPullback p₂) ⋙
    Functor.uncurry.obj (derivedTensorProductFunctor P.sheaf)

/-- **`Lδ^*(Lp₁^*K ⊗^L Lp₂^*M) ≅ K ⊗^L M`**, naturally in `(K, M)`, for a morphism of ringed
spaces `δ : X ⟶ P` with two retractions `p₁, p₂ : P ⟶ X`: the comparison of
[Stacks, Tag 079U] for `δ`, followed by `Lδ^*Lpᵢ^* ≅ 𝟭` in each factor. -/
def derivedRestrictionIso :
    exteriorDerivedTensor p₁ p₂ ⋙ derivedPullback δ ≅
      Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((derivedPullback p₁).prod (derivedPullback p₂))
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso δ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (derivedPullbackRetractionIso δ p₁ h₁) (derivedPullbackRetractionIso δ p₂ h₂))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)) ≪≫
    Functor.leftUnitor _

/-- The retraction isomorphism is the composition comparison of [Stacks, Tag 0D5S] followed by
the identification of `L(𝟙)^*` with the identity. -/
theorem derivedPullbackRetractionIso_hom (p : P ⟶ X) (h : δ ≫ p = 𝟙 X) :
    (derivedPullbackRetractionIso δ p h).hom =
      Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical δ p ≫
        eqToHom (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq h) ≫
        (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X).hom :=
  rfl

/-- **The defining formula of `derivedRestrictionIso`**: it is the comparison
`Lδ^*(A ⊗^L B) ≅ Lδ^*A ⊗^L Lδ^*B` of [Stacks, Tag 079U] at `A = Lp₁^*K`, `B = Lp₂^*M`, followed
by the retraction isomorphisms `Lδ^*Lp₁^*K ≅ K` and `Lδ^*Lp₂^*M ≅ M` in the two factors; the
associators and the unitor are identities. -/
theorem derivedRestrictionIso_hom :
    (derivedRestrictionIso δ p₁ p₂ h₁ h₂).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((derivedPullback p₁).prod (derivedPullback p₂))
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso δ).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (NatTrans.prod (derivedPullbackRetractionIso δ p₁ h₁).hom
            (derivedPullbackRetractionIso δ p₂ h₂).hom)
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)) ≫
        (Functor.leftUnitor _).hom :=
  rfl

end RingedSpace

section Scheme

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The diagonal is a section of the first projection, as morphisms of ringed spaces. -/
lemma diagonal_fst_toShHom :
    (pullback.diagonal f).toLRSHom.toShHom ≫ (pullback.fst f f).toLRSHom.toShHom =
      𝟙 X.toRingedSpace :=
  congrArg (fun g : X ⟶ X => g.toLRSHom.toShHom) (pullback.diagonal_fst f)

/-- The diagonal is a section of the second projection, as morphisms of ringed spaces. -/
lemma diagonal_snd_toShHom :
    (pullback.diagonal f).toLRSHom.toShHom ≫ (pullback.snd f f).toLRSHom.toShHom =
      𝟙 X.toRingedSpace :=
  congrArg (fun g : X ⟶ X => g.toLRSHom.toShHom) (pullback.diagonal_snd f)

/-- **The first isomorphism of part (2)**: `LΔ^*(Lpr₁^*K ⊗^L Lpr₂^*M) ≅ K ⊗^L M`, naturally in
the pair `(K, M)`. -/
def diagonalRestrictionIso :
    exteriorDerivedTensor (pullback.fst f f).toLRSHom.toShHom (pullback.snd f f).toLRSHom.toShHom ⋙
        derivedPullback (pullback.diagonal f).toLRSHom.toShHom ≅
      Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf) :=
  derivedRestrictionIso _ _ _ (diagonal_fst_toShHom f) (diagonal_snd_toShHom f)

variable [IsSeparated f]

/-- `𝒪_Δ = Δ_*𝒪_X`, the structure sheaf of the diagonal as an `𝒪_{X ×_S X}`-module. -/
abbrev diagonalStructureModule :
    SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace) :=
  (modulePushforward (pullback.diagonal f).toLRSHom.toShHom).obj
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))

/-- `Δ_*` on derived categories: the functor induced by the exact functor `Δ_*`. -/
abbrev diagonalPushforward :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace)) :=
  (modulePushforward (pullback.diagonal f).toLRSHom.toShHom).mapDerivedCategory

/-- `𝒪_Δ[0] ≅ Δ_*(𝒪_X[0])`. -/
def diagonalStructureModuleIso :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace)) 0).obj
          (diagonalStructureModule f) ≅
      Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion (pullback.diagonal f)) :=
  ((modulePushforward (pullback.diagonal f).toLRSHom.toShHom).mapDerivedCategorySingleFunctor
    0).app _ |>.symm

/-- **The second isomorphism of part (2)**:
`𝒪_Δ ⊗^L (Lpr₁^*K ⊗^L Lpr₂^*M) ≅ Δ_*(K ⊗^L M)`, naturally in the pair `(K, M)`. -/
def diagonalTensorIso :
    exteriorDerivedTensor (pullback.fst f f).toLRSHom.toShHom (pullback.snd f f).toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace)) 0).obj
          (diagonalStructureModule f)) ≅
      Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf) ⋙
        diagonalPushforward f :=
  Functor.isoWhiskerLeft _
      ((derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).mapIso
          (diagonalStructureModuleIso f) ≪≫
        Stacks.Duality.TensorHomTorAmplitude.tensorPushforwardStructureSheafNatIso
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion (pullback.diagonal f))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (diagonalRestrictionIso f) _

/-- **The defining formula of `diagonalTensorIso`**: the identification
`𝒪_Δ[0] ≅ Δ_*(𝒪_X[0])` in the first factor, then the projection formula of [Stacks, Tag 0B55] at
the structure sheaf (`Stacks.Duality.TensorHomTorAmplitude.tensorPushforwardStructureSheafNatIso`:
the projection-formula morphism of [Stacks, Tag 0B53] followed by the unit constraint), and then
`Δ_*` of `diagonalRestrictionIso`. -/
theorem diagonalTensorIso_hom :
    (diagonalTensorIso f).hom =
      Functor.whiskerLeft _
          ((derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).map
              (diagonalStructureModuleIso f).hom ≫
            (Stacks.Duality.TensorHomTorAmplitude.tensorPushforwardStructureSheafNatIso
              (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
                (pullback.diagonal f))).hom) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (diagonalRestrictionIso f).hom _ :=
  rfl

/-- **[Stacks, Tag 0B0T], part (2).** Let `f : X ⟶ S` be a separated morphism of schemes (for
instance a variety over a field) with projections `pr₁, pr₂ : X ×_S X ⟶ X` and diagonal `Δ`.
For `K, M ∈ D(𝒪_X)` there are canonical isomorphisms, natural in `(K, M)`,

* `LΔ^*(Lpr₁^*K ⊗^L Lpr₂^*M) ≅ K ⊗^L M` (the first component, `diagonalRestrictionIso`), and
* `𝒪_Δ ⊗^L (Lpr₁^*K ⊗^L Lpr₂^*M) ≅ Δ_*(K ⊗^L M)` (the second, `diagonalTensorIso`),

where `𝒪_Δ = Δ_*𝒪_X` is placed in degree zero. They are the composites of canonical maps recorded
by `derivedRestrictionIso_hom` and `diagonalTensorIso_hom`: the comparison of [Stacks, Tag 079U]
with the composition isomorphisms of [Stacks, Tag 0D5S], and the projection formula of
[Stacks, Tag 0B55]. The source's hypotheses (`X` a nonsingular variety, `K, M ∈ D_QCoh(𝒪_X)`)
are not needed beyond separatedness; `D_QCoh(𝒪_X)` being a full subcategory, these are in
particular isomorphisms in `D_QCoh`. -/
@[stacks 0B0T "(2)"]
def derivedDiagonalIsos :
    (exteriorDerivedTensor (pullback.fst f f).toLRSHom.toShHom (pullback.snd f f).toLRSHom.toShHom ⋙
        derivedPullback (pullback.diagonal f).toLRSHom.toShHom ≅
      Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf)) ×
    (exteriorDerivedTensor (pullback.fst f f).toLRSHom.toShHom (pullback.snd f f).toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace)) 0).obj
          (diagonalStructureModule f)) ≅
      Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf) ⋙
        diagonalPushforward f) :=
  (diagonalRestrictionIso f, diagonalTensorIso f)

end Scheme

end Stacks.Intersection.Diagonal
