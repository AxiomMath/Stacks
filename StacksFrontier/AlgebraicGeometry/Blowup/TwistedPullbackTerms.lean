module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedDirectSums
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOverABase
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.DerivedPullbackOfATilde
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic
public import StacksFrontier.Homology.KFlat.FreeResolution
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRight
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a twisted derived pullback along the affine blowup

Let `A` be a commutative ring, `I ⊆ A` an ideal, and `p : X ⟶ Spec A` the blowup of `Spec A` in
`I`, so that `X = Proj(⨁_{n ≥ 0} Iⁿ)` carries the twists `𝒪_X(q)`. For a free `A`-module `N` the
pullback `p^*(Ñ)` is a direct sum of copies of `𝒪_X`, so its twist is a direct sum of copies of
`𝒪_X(q)`:

`p^*(Ñ) ⊗_{𝒪_X} 𝒪_X(q) ≅ ⨁_{j ∈ J} 𝒪_X(q)`, `J` a basis of `N`.

For an `A`-module `M` with a K-flat resolution `P^• ⟶ M` by free `A`-modules, the derived tensor
product `Lp^*(M̃) ⊗^𝐋 𝒪_X(q)` is the total complex `Tot(p^*P̃^• ⊗_{𝒪_X} 𝒪_X(q)[0])`, whose
degree-`i` term is a direct sum of copies of `𝒪_X(q)`. When `𝒪_X(q)` has no higher cohomology,
as it does above the threshold of [Stacks, Tag 0AG7], the complex of `A`-linear global sections
of this total complex computes `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(q))` in `D(A)`.

## Main results

* `Stacks.Blowup.pullbackTildeTwistIsoCoproduct`: the twist of the pullback of the sheafification
  of a free module is a direct sum of copies of the twist.
* `Stacks.Blowup.tensorComplexTwistXIsoCoproduct` and
  `Stacks.Blowup.twistedPullbackComplexXIsoCoproduct`: the terms of the total tensor complex
  `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` are direct sums of copies of the twist, for `P^•` a complex of free
  modules, at the two spellings of the total complex.
* `Stacks.Blowup.isQuasicoherent_coproduct_blowUpTwist`: a direct sum of copies of a twist is
  quasi-coherent.
* `Stacks.Blowup.isIso_derivedGlobalSectionsOverUnit_tensorComplexTwist`: the complex of
  `A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` computes its `A`-linear derived global
  sections, granted the vanishing of [Stacks, Tag 0AG7] for `𝒪_X(q)`.
* `Stacks.Blowup.derivedTwistedPullbackIso`: the derived tensor product
  `Lp^*(M̃) ⊗^𝐋 𝒪_X(q)` is the total complex `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])`.
* `Stacks.Blowup.derivedGlobalSectionsTwistedPullbackIso`: `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(q))` is the
  complex of `A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])`, in `D(A)`.

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPullbackOfATilde

universe u

namespace Stacks.Blowup

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The affine blowup, read as a ringed space. -/
abbrev blowUpRingedSpace : RingedSpace.{u, u} := (blowUpSpec I).toRingedSpace

/-- The structure morphism of the affine blowup, read as a morphism of ringed spaces. -/
abbrev toSpecRingedSpace :
    blowUpRingedSpace I ⟶ (Spec (CommRingCat.of A)).toRingedSpace :=
  (toSpec I).toLRSHom.toShHom

/-- Sheaves of modules on the affine blowup, with the sheaf of rings written at the spelling the
tensor bifunctor is stated over. -/
abbrev BlowUpModules : Type (u + 1) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (blowUpRingedSpace I).sheaf)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The total complexes `Tot(K₁ ⊗_{𝒪_X} K₂)` on the affine blowup exist. -/
local instance hasMapBifunctorSheafTensor :
    ∀ K₁ K₂ : CochainComplex (BlowUpModules I) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor (blowUpRingedSpace I).sheaf)
        (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor (blowUpRingedSpace I).sheaf

/-- A twist on the affine blowup is quasi-coherent. -/
instance isQuasicoherent_blowUpTwist (q : ℤ) : (blowUpTwist I q).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf
    (reesGrading I) q

/-- The twist of the pullback of the sheafification of a free module is a direct sum of copies
of the twist, indexed by a basis of the module. -/
def pullbackTildeTwistIsoCoproduct {J : Type u} (N : ModuleCat.{u} (CommRingCat.of A))
    (b : Module.Basis J (CommRingCat.of A) N) (q : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (blowUpRingedSpace I).sheaf).obj
          ((modulePullback (toSpecRingedSpace I)).obj
            ((tildeFunctor (CommRingCat.of A)).obj N))).obj (blowUpTwist I q) ≅
      ∐ fun _ : J => blowUpTwist I q :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
        (blowUpRingedSpace I).sheaf).flip.obj (blowUpTwist I q)).mapIso
      (modulePullbackTildeFreeIsoCoproduct (toSpecRingedSpace I) N b) ≪≫
    Stacks.SheafOfModules.Strict.coproductUnitTensorIso
      (blowUpRingedSpace I).sheaf (blowUpTwist I q) J

/-- The degreewise pullback along `p` of the degreewise sheafification of a complex of
`A`-modules, with its type written at the spelling of the sheaf of rings that the tensor
bifunctor is stated over. -/
def pullbackTildeComplex (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) :
    CochainComplex (BlowUpModules I) ℤ :=
  ((modulePullback (toSpecRingedSpace I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (tildeComplex P)

/-- The terms of the total tensor complex `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` are direct sums of copies
of the twist, for `P^•` a complex of free `A`-modules. -/
def tensorComplexTwistXIsoCoproduct
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) (CommRingCat.of A) (P.X i)) (q : ℤ) (i : ℤ) :
    (HomologicalComplex.mapBifunctor
          (pullbackTildeComplex I P)
          ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))
          (Stacks.SheafOfModules.Tensor.sheafTensor (blowUpRingedSpace I).sheaf)
          (ComplexShape.up ℤ)).X i ≅
      ∐ fun _ : J i => blowUpTwist I q :=
  HomologicalComplex.mapBifunctorSingleRightXIso
      (Stacks.SheafOfModules.Tensor.sheafTensor (blowUpRingedSpace I).sheaf)
      (pullbackTildeComplex I P) (blowUpTwist I q) i ≪≫
    pullbackTildeTwistIsoCoproduct I (P.X i) (b i) q

/-- The total tensor complex `Tot(p^*P̃^• ⊗_{𝒪_X} 𝒪_X(q)[0])`. -/
def twistedPullbackComplex (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (q : ℤ) :
    CochainComplex (BlowUpModules I) ℤ :=
  ((Stacks.SheafOfModules.Tensor.tensorComplex (blowUpRingedSpace I).sheaf).obj
      (pullbackTildeComplex I P)).obj
    ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))

/-- The terms of the total tensor complex `twistedPullbackComplex I P q` are direct sums of
copies of the twist, for `P^•` a complex of free `A`-modules. -/
def twistedPullbackComplexXIsoCoproduct
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) (CommRingCat.of A) (P.X i)) (q : ℤ) (i : ℤ) :
    (twistedPullbackComplex I P q).X i ≅ ∐ fun _ : J i => blowUpTwist I q :=
  tensorComplexTwistXIsoCoproduct I P b q i

/-- A direct sum of copies of a twist on the affine blowup is quasi-coherent. -/
theorem isQuasicoherent_coproduct_blowUpTwist (q : ℤ) (J : Type u) :
    (∐ fun _ : J => blowUpTwist I q).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun _ : J => blowUpTwist I q) fun _ =>
    inferInstanceAs (blowUpTwist I q).IsQuasicoherent

variable [IsNoetherianRing A]

/-- The complex of `A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` computes its
`A`-linear derived global sections, provided `𝒪_X(q)` has no higher cohomology (the vanishing of
[Stacks, Tag 0AG7]). -/
theorem isIso_derivedGlobalSectionsOverUnit_tensorComplexTwist
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) (CommRingCat.of A) (P.X i)) (q : ℤ)
    (hvanish : ∀ j : ℤ, 0 < j →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus j).obj
        (blowUpTwist I q))) :
    IsIso ((AlgebraicGeometry.derivedGlobalSectionsOverUnit (toSpec I)).app
      ((HomotopyCategory.quotient (blowUpSpec I).Modules (ComplexShape.up ℤ)).obj
        (twistedPullbackComplex I P q))) :=
  AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_of_termwise_acyclic (toSpec I) _
    (fun i => (SheafOfModules.isQuasicoherent (blowUpSpec I).ringCatSheaf).prop_of_iso
      (twistedPullbackComplexXIsoCoproduct I P b q i).symm
      (isQuasicoherent_coproduct_blowUpTwist I q (J i)))
    fun i => AlgebraicGeometry.rightAcyclic_sectionsFunctor_of_iso_coproduct (blowUpSpec I)
      (fun _ : J i => blowUpTwist I q) _ (twistedPullbackComplexXIsoCoproduct I P b q i)
      fun j hj _ => hvanish j hj

/-- The derived category of sheaves of modules on the affine blowup, at the spelling
`Stacks.DerivedTensor.RingedSite.Modules` of the category of modules. -/
local instance hasDerivedCategoryBlowUpModules :
    HasDerivedCategory.{u + 1}
      (Stacks.DerivedTensor.RingedSite.Modules (blowUpRingedSpace I).sheaf) :=
  inferInstanceAs (HasDerivedCategory.{u + 1} (BlowUpModules I))

/-- The derived tensor product `Lp^*(M̃) ⊗^𝐋 𝒪_X(q)` is the total tensor complex
`Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` of a K-flat resolution `P^•` of `M`. -/
def derivedTwistedPullbackIso (M : ModuleCat.{u} (CommRingCat.of A))
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)
    (hg : QuasiIso g) (q : ℤ) :
    ((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
              ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))))).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))) ≅
      DerivedCategory.Q.obj (twistedPullbackComplex I P q) :=
  ((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.mapIso
        (derivedPullbackTildeSingleIso (toSpecRingedSpace I) M P hP g hg)).app _ ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).comparisonRight
      (pullbackTildeComplex I P) _ (kFlat_singleFunctor_twistingSheaf_reesGrading I q)

/-- Derived global sections of the twisted derived pullback are the `A`-linear global sections of
the total tensor complex of a free resolution: `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(q))` is the complex of
`A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` in `D(A)`, provided `𝒪_X(q)` has no
higher cohomology (the vanishing of [Stacks, Tag 0AG7]). -/
def derivedGlobalSectionsTwistedPullbackIso (M : ModuleCat.{u} (CommRingCat.of A))
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)
    (hg : QuasiIso g) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) (CommRingCat.of A) (P.X i)) (q : ℤ)
    (hvanish : ∀ j : ℤ, 0 < j →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus j).obj
        (blowUpTwist I q))) :
    (AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
                  M))))).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q)))) ≅
      (AlgebraicGeometry.homotopyGlobalSectionsOver (toSpec I)).obj
        ((HomotopyCategory.quotient (blowUpSpec I).Modules (ComplexShape.up ℤ)).obj
          (twistedPullbackComplex I P q)) :=
  letI := isIso_derivedGlobalSectionsOverUnit_tensorComplexTwist I P b q hvanish
  (AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).mapIso
      (derivedTwistedPullbackIso I M P hP g hg q) ≪≫
    (AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).mapIso
      ((DerivedCategory.quotientCompQhIso (blowUpSpec I).Modules).app
        (twistedPullbackComplex I P q)).symm ≪≫
    (asIso ((AlgebraicGeometry.derivedGlobalSectionsOverUnit (toSpec I)).app
      ((HomotopyCategory.quotient (blowUpSpec I).Modules (ComplexShape.up ℤ)).obj
        (twistedPullbackComplex I P q)))).symm

end Stacks.Blowup

end
