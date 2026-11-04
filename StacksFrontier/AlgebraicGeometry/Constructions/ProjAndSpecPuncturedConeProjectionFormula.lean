module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedCoproduct
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image of a pullback to the punctured cone

Let `A` be a nonnegatively graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached to
cone data for `A`, with punctured cone `U ⊆ L` and restricted projection `π|_U : U ⟶ P`. For a
quasi-coherent `𝒪_P`-module `𝓕` this file computes the direct image of its pullback,

  `(π|_U)_*(π|_U)^*𝓕 = ⨁_{m ∈ ℤ} 𝓕 ⊗_{𝒪_P} 𝒪_P(m)`,

out of the identification `(π|_U)_*𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. This is the
step that the source performs between the sentence "`π|_U` is affine with
`(π|_U)_*𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)`" and the display

  `R(π|_U)_*𝓕_U = (π|_U)_*(π|_U)^*𝓕 = ⨁_{m ∈ ℤ} 𝓕 ⊗_{𝒪_P} 𝒪_P(m)`

of [Stacks, Tag 0EKH]. Feeding the result to
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso` gives the decomposition
of the derived global sections themselves,

  `RΓ(U, 𝓕_U) = ⨁_{m ∈ ℤ} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`,

which is the equation of [Stacks, Tag 0EKH] itself. For the cone of the truncation algebra
`B = ⨁_{d ≥ 0} A_{≥ d}` — the cone of the source's situation — the input from
[Stacks, Tag 0EKG] is supplied by
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso`, so the
last two declarations below assume nothing beyond quasi-compactness of `P` and quasi-coherence
of `𝓕`, which are the source's own hypotheses.

Two facts do the work. The projection formula along an affine morphism ([Stacks, Tag 0FZE])
turns `(π|_U)_*(π|_U)^*𝓕` into `𝓕 ⊗_{𝒪_P} (π|_U)_*𝒪_U`, once the pullback is written as
`𝒪_U ⊗_{𝒪_U} (π|_U)^*𝓕` by the left unit constraint; and tensoring with a fixed sheaf of modules
preserves colimits ([Stacks, Tag 05NB]), so the direct sum passes out of the tensor product.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpec.projTensorLeft`: tensoring `𝒪_P`-modules on the left by
  a fixed one, as a functor; `projTensorLeft_obj_twistingSheaf` identifies its value at `𝒪_P(m)`
  with the twist `𝓕(m)`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeStructurePushforward`: the direct image
  `(π|_U)_*𝒪_U`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.tensorCoproductTwistIso`:
  `𝓕 ⊗_{𝒪_P} (⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ ⨁_{m ∈ ℤ} 𝓕(m)`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardTensorIso`:
  `(π|_U)_*(π|_U)^*𝓕 ≅ 𝓕 ⊗_{𝒪_P} (π|_U)_*𝒪_U`, the projection formula along `π|_U`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardPullbackCoproductIso`:
  **`(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_{m ∈ ℤ} 𝓕(m)`**, the two combined.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoOfStructureIso`:
  the decomposition of the derived direct image that [Stacks, Tag 0EKH] displays, for arbitrary
  cone data, with the `𝓕`-dependent hypothesis of
  `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso` discharged and only
  the identification of [Stacks, Tag 0EKG] left as an input.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardPullbackCoproductIsoTruncation`
  and
  `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation`: the same
  two for the cone of the truncation algebra, **with nothing assumed** — the latter is
  `RΓ(U, 𝓕_U) = ⨁_{m ∈ ℤ} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`, the equation of [Stacks, Tag 0EKH].

## Implementation notes

*Which spelling of the tensor product.* The twist
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`
is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the sheafification of the objectwise
tensor product, with the module in the left factor. `projTensorLeft` is
`Stacks.SheafOfModules.TensorColimits.tensorLeft`, which is that same construction read as a
functor of the right factor, so `projTensorLeft_obj` and `projTensorLeft_obj_twistingSheaf` hold
by `rfl`; and the projection formula is stated at `Stacks.RingedSpace.tensorSheaf`, which is
again the same sheaf. No transport between the three spellings is needed.

*The index universe.* Tensoring preserves colimits indexed by categories of the module universe,
whereas the grading of the twists is indexed by `ℤ`, which lives in `Type 0`. The instance below
transports the preservation statement along `Discrete (ULift ℤ) ≌ Discrete ℤ`, exactly as
`Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_int_singleFunctor` does for
the derived category.

*Why the unconditional form is stated for the truncation algebra.* The identification
`(π|_U)_*𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG] is available for the cone of
`B = ⨁_{d ≥ 0} A_{≥ d}`, which is the cone the source constructs; it is carried for arbitrary
cone data as a hypothesis, since the proof of the identification computes in `B`. The source sets
`B = ⨁_{d ≥ 0} A_{≥ d}` and builds `L = Proj B` from it, so the unconditional declarations are
stated in the source's own situation; `Stacks.AlgebraicGeometry.ProjAndSpecTruncation` is where
that `B` is exhibited as cone data, and `Stacks.Truncation.truncationAlgebra_unique` pins it down
up to a unique isomorphism compatible with the identifications `A_{≥ d} ≃+ B_d`.

## References

* [Stacks Project, Tag 0EKH](https://stacks.math.columbia.edu/tag/0EKH)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.ProjAndSpec

section Site

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The structure sheaf of `Proj 𝒜`, as a presheaf of (not necessarily commutative) rings, is a
sheaf. -/
theorem isSheaf_projStructureRingPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj) :=
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).property

/-- Tensoring sheaves of modules on `P = Proj 𝒜` on the left by a fixed `𝓕`. -/
def projTensorLeft (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    (AlgebraicGeometry.Proj 𝒜).Modules ⥤ (AlgebraicGeometry.Proj 𝒜).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
    ((ProjectiveSpectrum.Proj.structureSheaf 𝒜))).obj F

/-- The value of `projTensorLeft 𝒜 F` at `𝓖` is the tensor product `𝓕 ⊗_{𝒪_P} 𝓖` of sheaves
of modules. -/
theorem projTensorLeft_obj (F G : (AlgebraicGeometry.Proj 𝒜).Modules) :
    (projTensorLeft 𝒜 F).obj G =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj,
          Presheaf.isSheaf_of_isSheaf_comp _ ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj)
            (forget₂ CommRingCat RingCat) ((isSheaf_projStructureRingPresheaf 𝒜))⟩).obj
          (F)).obj (G)) :=
  rfl

/-- The value of `projTensorLeft 𝒜 F` at the twisting sheaf `𝒪_P(m)` is the twist
`𝓕(m) = 𝓕 ⊗_{𝒪_P} 𝒪_P(m)`. -/
theorem projTensorLeft_obj_twistingSheaf (F : (AlgebraicGeometry.Proj 𝒜).Modules) (m : ℤ) :
    (projTensorLeft 𝒜 F).obj (twistingSheaf 𝒜 m) = twistSheafOfModules 𝒜 F m :=
  rfl

/-- Tensoring `𝒪_P`-modules on the left by a fixed `𝓕` preserves `ℤ`-indexed coproducts. -/
instance preservesColimitsOfShape_discrete_int_projTensorLeft
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    PreservesColimitsOfShape (Discrete ℤ) (projTensorLeft 𝒜 F) :=
  have hL : PreservesColimitsOfSize.{u, u} (projTensorLeft 𝒜 F) :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜) F
  have : PreservesColimitsOfShape (Discrete (ULift.{u, 0} ℤ)) (projTensorLeft 𝒜 F) :=
    hL.preservesColimitsOfShape
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℤ))) _

/-- **`𝓕 ⊗ (⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ ⨁_{m ∈ ℤ} 𝓕(m)`.** -/
def tensorCoproductTwistIso (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    (projTensorLeft 𝒜 F).obj (∐ fun m : ℤ => twistingSheaf 𝒜 m) ≅
      ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m :=
  PreservesCoproduct.iso (projTensorLeft 𝒜 F) fun m : ℤ => twistingSheaf 𝒜 m

end Site

section Cone

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ)

/-- **The direct image `(π|_U)_* 𝒪_U` of the structure sheaf of the punctured cone.** -/
abbrev puncturedConeStructurePushforward : (AlgebraicGeometry.Proj 𝒜).Modules :=
  (Scheme.Modules.pushforward (puncturedConeProj c)).obj
    (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)

/-- **`(π|_U)_*(π|_U)^*𝓕 ≅ 𝓕 ⊗_{𝒪_P} (π|_U)_*𝒪_U`**, the projection formula along the affine
morphism `π|_U`. -/
def puncturedConePushforwardTensorIso (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent] :
    (Scheme.Modules.pushforward (puncturedConeProj c)).obj (puncturedConePullback c F) ≅
      (projTensorLeft 𝒜 F).obj (puncturedConeStructurePushforward c) :=
  have : IsAffineHom (puncturedConeProj c) := isAffineHom_pi_restrict c
  have hu := Stacks.SheafOfModules.tensorSheafLeftUnitor
    (openUInL c).toScheme.presheaf (openUInL c).toScheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (puncturedConeProj c)).obj F)
  ((Scheme.Modules.pushforward (puncturedConeProj c)).mapIso hu).symm ≪≫
    (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent
      (puncturedConeProj c) (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf) F
      (AffineQcohPushforward.isQuasicoherent_unit _) ‹F.IsQuasicoherent›).symm ≪≫
    Stacks.SheafOfModules.tensorSheafBraiding _ (isSheaf_projStructureRingPresheaf 𝒜) _ F

/-- **`(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_{m ∈ ℤ} 𝓕 ⊗_{𝒪_P} 𝒪_P(m)`**, from the identification
`(π|_U)_*𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. -/
def puncturedConePushforwardPullbackCoproductIso (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent]
    (h0 : puncturedConeStructurePushforward c ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m) :
    (Scheme.Modules.pushforward (puncturedConeProj c)).obj (puncturedConePullback c F) ≅
      ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m :=
  puncturedConePushforwardTensorIso c F ≪≫ (projTensorLeft 𝒜 F).mapIso h0 ≪≫
    tensorCoproductTwistIso 𝒜 F

/-- **`RΓ(U, 𝓕_U) = ⨁_{m ∈ Z} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`.** Derived global sections of the
pullback of a quasi-coherent `𝒪_P`-module `𝓕` to the punctured cone decompose as the direct sum,
over all integers `m`, of the derived global sections of the `m`-th twist of `𝓕`; both sides are
read as derived direct images to `Z = Spec A₀`.

This is `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso` with its
hypothesis on `𝓕` discharged by the projection formula, leaving only the `𝓕`-independent
identification `(π|_U)_*𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. For the cone of the
truncation algebra — the cone of the source's situation — that identification is
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso`, and
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation` is this
isomorphism with nothing assumed. -/
def derivedPushforwardPuncturedConeIsoOfStructureIso
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent]
    (h0 : puncturedConeStructurePushforward c ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m) :
    (Stacks.Duality.derivedPushforward
          (puncturedConeProj c ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (puncturedConePullback c F)) ≅
      ∐ fun m : ℤ => (Stacks.Duality.derivedPushforward
        (AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistSheafOfModules 𝒜 F m)) :=
  derivedPushforwardPuncturedConeIso c F
    (puncturedConePushforwardPullbackCoproductIso c F h0)

end Cone

section Truncation

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- **`(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_{m ∈ ℤ} 𝓕 ⊗_{𝒪_P} 𝒪_P(m)`** for the cone of the truncation
algebra `B = ⨁_{d ≥ 0} A_{≥ d}`, with nothing assumed. -/
def puncturedConePushforwardPullbackCoproductIsoTruncation
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pushforward (puncturedConeProj (truncationConeData 𝒜))).obj
        (puncturedConePullback (truncationConeData 𝒜) F) ≅
      ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m :=
  puncturedConePushforwardPullbackCoproductIso (truncationConeData 𝒜) F
    (Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso 𝒜)

/-- **`RΓ(U, 𝓕_U) = ⨁_{m ∈ Z} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`.** Let `A` be a nonnegatively graded
ring, `P = Proj A` quasi-compact, `π : L ⟶ P` the cone of the truncation algebra
`B = ⨁_{d ≥ 0} A_{≥ d}` and `U ⊆ L` the punctured cone. For a quasi-coherent `𝒪_P`-module `𝓕`
with pullback `𝓕_U = (π|_U)^*𝓕`, the derived global sections of `𝓕_U` decompose as the direct
sum, over all integers `m`, of the derived global sections of the `m`-th twist of `𝓕`; both sides
are read as derived direct images to `Z = Spec A₀`. -/
@[stacks 0EKH "the direct-sum decomposition, with RΓ read as derived direct image to Spec A₀"]
def derivedPushforwardPuncturedConeIsoTruncation
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent] :
    (Stacks.Duality.derivedPushforward
          (puncturedConeProj (truncationConeData 𝒜) ≫
            AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (puncturedConePullback (truncationConeData 𝒜) F)) ≅
      ∐ fun m : ℤ => (Stacks.Duality.derivedPushforward
        (AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistSheafOfModules 𝒜 F m)) :=
  derivedPushforwardPuncturedConeIsoOfStructureIso (truncationConeData 𝒜) F
    (Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso 𝒜)

end Truncation

end Stacks.AlgebraicGeometry.ProjAndSpec

end
