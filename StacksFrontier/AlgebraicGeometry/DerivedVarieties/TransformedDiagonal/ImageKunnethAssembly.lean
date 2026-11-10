module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.DegreeZeroVanishing
public import
  StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransportKunneth
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtFibreProduct
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroHomNaturality
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoxSheafHomMapNaturality
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroUnitIso

/-!
# The Künneth input `himage` of Tag 0G0A, assembled at the standard model

For `X`, `Y` over a field `k`, `W = X ×_k Y`, perfect `K ∈ D(𝒪_X)`, `M ∈ D(𝒪_Y)` and any
`K'`, `M'`, the chain

`Hom(K, K') ⊗_k Hom(M, M') ≃ H⁰RΓ(X, R𝓗om(K, K')) ⊗_k H⁰RΓ(Y, R𝓗om(M, M'))`
`  ≃ H⁰RΓ(W, Lp^*R𝓗om(K, K') ⊗^𝐋 Lq^*R𝓗om(M, M'))`
`  ≃ H⁰RΓ(W, R𝓗om(K ⊠ M, K' ⊠ M')) ≃ Hom(K ⊠ M, K' ⊠ M')`

is [Stacks, Tag 08DK] on `X` and `Y`, the degree-zero Künneth isomorphism
(`AlgebraicGeometry.degreeZeroKunnethLinearEquiv`, from [Stacks, Tag 0FLQ]), `H⁰RΓ` of the
comparison `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap` (invertible at perfect sources by
[Stacks, Tag 0GM7] (1), [Stacks, Tag 0FXP] and [Stacks, Tag 09UA]), and 08DK on `W`. Once one
knows that this chain sends `a ⊗ c` to `a ⊠ c` (`AlgebraicGeometry.DegreeZeroPureTensorLaw`), the
pairing `(a, c) ↦ a ⊠ c` exhibits `Hom(K ⊠ M, K' ⊠ M')` as the tensor product.

## Main results

* `AlgebraicGeometry.isTensorPairing_of_degreeZeroKunneth`: the chain, for any perfect `K`, `M`.
* `AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_law`: at the
  terms `ℰᵢ ⊠ F(𝒢ᵢ)` of Tag 0G0A, which with
  `AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairing_iff_std` is the
  hypothesis `himage`.

## References

* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedKunnethExt (boxSheafHomMap boxProd sheafHomObj tensorMap
  derivedPullbackFunctor)

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- `H⁰RΓ(W, -)` of the comparison
`Lp^*R𝓗om(K, K') ⊗^𝐋 Lq^*R𝓗om(M, M') ⟶ R𝓗om(K ⊠ M, K' ⊠ M')` of
`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`, on `W = X ×_k Y` over `Spec k`. -/
abbrev degreeZeroBoxSheafHomMap (K K' : DerivedCategory X.Modules)
    (M M' : DerivedCategory Y.Modules) :
    degreeZeroSections k (pullback.fst f g ≫ f)
        (boxDerived k f g (sheafHomObj X.toRingedSpace K K') (sheafHomObj Y.toRingedSpace M M')) ⟶
      degreeZeroSections k (pullback.fst f g ≫ f)
        (sheafHomObj (pullback f g).toRingedSpace
          (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom K M)
          (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom
            K' M')) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
    ((sectionsOverBase (pullback.fst f g ≫ f).toLRSHom.toShHom).map
      (boxSheafHomMap (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom
        K K' M M'))

/-- **`boxSheafHomMap` is invertible at perfect sources**, on `W = X ×_k Y`: the two pullback
comparisons of [Stacks, Tag 08I3] are invertible at a perfect source by [Stacks, Tag 0GM7] (1),
and the comparison of [Stacks, Tag 0FXP] on `W` at the perfect objects `Lp^*K`, `Lq^*M`
([Stacks, Tag 09UA]), exactly as in the proof of
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_fibreProduct`. -/
theorem isIso_boxSheafHomMap_of_isPerfect (K K' : DerivedCategory X.Modules)
    (M M' : DerivedCategory Y.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hM : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) M) :
    IsIso (boxSheafHomMap (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom
      K K' M M') :=
  Stacks.Cohomology.DerivedKunnethExt.isIso_boxSheafHomMap (pullback.fst f g).toLRSHom.toShHom
    (pullback.snd f g).toLRSHom.toShHom K K' M M'
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
      (pullback.fst f g).toLRSHom.toShHom K hK K')
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
      (pullback.snd f g).toLRSHom.toShHom M hM M')
    (Stacks.Cohomology.DerivedKunnethExt.isIso_sheafHomTensorMap_of_isPerfect_space
      (pullback f g).toRingedSpace
      ((derivedPullbackFunctor (pullback.fst f g).toLRSHom.toShHom).obj K)
      ((derivedPullbackFunctor (pullback.fst f g).toLRSHom.toShHom).obj K')
      ((derivedPullbackFunctor (pullback.snd f g).toLRSHom.toShHom).obj M)
      ((derivedPullbackFunctor (pullback.snd f g).toLRSHom.toShHom).obj M')
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (pullback.fst f g).toLRSHom.toShHom K hK)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (pullback.snd f g).toLRSHom.toShHom M hM))

/-- `H⁰RΓ(W, -)` of `boxSheafHomMap` is invertible at perfect sources. -/
theorem isIso_degreeZeroBoxSheafHomMap (K K' : DerivedCategory X.Modules)
    (M M' : DerivedCategory Y.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hM : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) M) :
    IsIso (degreeZeroBoxSheafHomMap k f g K K' M M') := by
  have h1 : IsIso (boxSheafHomMap (pullback.fst f g).toLRSHom.toShHom
      (pullback.snd f g).toLRSHom.toShHom K K' M M') :=
    isIso_boxSheafHomMap_of_isPerfect k f g K K' M M' hK hM
  exact ((DerivedCategory.homologyFunctor _ 0).mapIso
    ((sectionsOverBase (pullback.fst f g ≫ f).toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ _ h1))).isIso_hom

/-- `H⁰RΓ(W, -)` of `boxSheafHomMap` at perfect sources, as a `k`-linear equivalence. -/
def degreeZeroBoxSheafHomLinearEquiv (K K' : DerivedCategory X.Modules)
    (M M' : DerivedCategory Y.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hM : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) M) :
    degreeZeroSectionsField k (pullback.fst f g ≫ f)
        (boxDerived k f g (sheafHomObj X.toRingedSpace K K')
          (sheafHomObj Y.toRingedSpace M M')) ≃ₗ[k]
      degreeZeroSectionsField k (pullback.fst f g ≫ f)
        (sheafHomObj (pullback f g).toRingedSpace
          (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom K M)
          (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom
            K' M')) :=
  haveI := isIso_degreeZeroBoxSheafHomMap k f g K K' M M' hK hM
  ((ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).mapIso
    (asIso (degreeZeroBoxSheafHomMap k f g K K' M M'))).toLinearEquiv

/-- The `k`-linear equivalence is the map it comes from. -/
theorem degreeZeroBoxSheafHomLinearEquiv_apply (K K' : DerivedCategory X.Modules)
    (M M' : DerivedCategory Y.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hM : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) M) (x) :
    degreeZeroBoxSheafHomLinearEquiv k f g K K' M M' hK hM x =
      (degreeZeroBoxSheafHomMap k f g K K' M M').hom x :=
  rfl

section Criterion

variable {k : Type*} [CommRing k] {M N P V : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup P] [AddCommGroup V] [Module k V]

/-- **A pairing that becomes a `k`-linear equivalence out of `M ⊗_k N` after an injective
additive map exhibits its target as the tensor product.** -/
theorem isTensorPairing_of_injective (D : P →+ V) (hD : Function.Injective D)
    (Θ : M ⊗[k] N ≃ₗ[k] V) (p : FreeAbelianGroup (M × N) →+ P)
    (h : ∀ m n, D (p (FreeAbelianGroup.of (m, n))) = Θ (m ⊗ₜ[k] n)) :
    IsTensorPairing k M N p := by
  have hcomp : ∀ u, D (p u) = Θ (freeAbelianGroupToTensor k M N u) := by
    intro u
    induction u using FreeAbelianGroup.induction_on with
    | zero => simp
    | of mn => rw [h, freeAbelianGroupToTensor_of]
    | neg mn h => rw [map_neg, map_neg, h, map_neg, map_neg]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := surjective_freeAbelianGroupToTensor k M N (Θ.symm (D y))
    exact ⟨u, hD (by rw [hcomp, hu, LinearEquiv.apply_symm_apply])⟩
  · ext u
    simp only [AddMonoidHom.mem_ker]
    refine ⟨fun h0 => ?_, fun h0 => hD (by rw [hcomp, h0, map_zero, map_zero])⟩
    have := hcomp u
    rw [h0, map_zero] at this
    exact Θ.map_eq_zero_iff.1 this.symm

end Criterion

/-- **The degree-zero Künneth assembly.** Let `K, M` be perfect, let `R𝓗om(K, K')` and
`R𝓗om(M, M')` satisfy the hypotheses of `AlgebraicGeometry.isIso_degreeZeroKunnethMap`, and let
`σ₁, σ₂` identify `M₁, M₂` `k`-linearly with their `H⁰RΓ`. A pairing into `P` whose values, read in
`H⁰RΓ(W, R𝓗om(K ⊠ M, K' ⊠ M'))` through an injective additive `D`, are the images of `σ₁ a ⊗ σ₂ c`
under the degree-zero Künneth map followed by `H⁰RΓ(boxSheafHomMap)`, exhibits `P` as
`M₁ ⊗_k M₂`. -/
theorem isTensorPairing_of_degreeZeroKunneth
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K K' : DerivedCategory X.Modules) (M M' : DerivedCategory Y.Modules)
    (hKp : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hMp : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) M)
    (hK : IsQCohAll (sheafHomObj X.toRingedSpace K K'))
    (hM : IsQCohAll (sheafHomObj Y.toRingedSpace M M'))
    (hK₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj (sheafHomObj X.toRingedSpace K K'))))
    (hM₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase g.toLRSHom.toShHom).obj (sheafHomObj Y.toRingedSpace M M'))))
    {M₁ M₂ P : Type*} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
    [AddCommGroup P]
    (σ₁ : M₁ ≃ₗ[k] degreeZeroSectionsField k f (sheafHomObj X.toRingedSpace K K'))
    (σ₂ : M₂ ≃ₗ[k] degreeZeroSectionsField k g (sheafHomObj Y.toRingedSpace M M'))
    (D : P →+ degreeZeroSectionsField k (pullback.fst f g ≫ f)
      (sheafHomObj (pullback f g).toRingedSpace
        (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom K M)
        (boxProd (pullback.fst f g).toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom K' M')))
    (hD : Function.Injective D) (pr : FreeAbelianGroup (M₁ × M₂) →+ P)
    (h : ∀ a c, D (pr (FreeAbelianGroup.of (a, c))) =
      (degreeZeroBoxSheafHomMap k f g K K' M M').hom
        ((degreeZeroKunnethMap k f g (sheafHomObj X.toRingedSpace K K')
          (sheafHomObj Y.toRingedSpace M M')).hom (σ₁ a ⊗ₜ σ₂ c))) :
    IsTensorPairing k M₁ M₂ pr :=
  isTensorPairing_of_injective D hD
    (TensorProduct.congr σ₁ σ₂ ≪≫ₗ degreeZeroKunnethLinearEquiv k f g _ _ hK hM hK₀ hM₀ ≪≫ₗ
      degreeZeroBoxSheafHomLinearEquiv k f g K K' M M' hKp hMp) pr fun a c => by
    rw [h]
    rfl

/-! ### The single functor, `k`-linearly -/

section Single

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Linear k C]

/-- `Hom(A, B) ≃ Hom(A[0], B[0])`, `k`-linearly: the single functor in degree zero is fully
faithful and `k`-linear. -/
def singleFunctorHomLinearEquiv (A B : C) :
    (A ⟶ B) ≃ₗ[k]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.singleFunctor C 0).obj B) where
  toFun := (DerivedCategory.singleFunctor C 0).map
  map_add' _ _ := (DerivedCategory.singleFunctor C 0).map_add
  map_smul' r x := (DerivedCategory.singleFunctor C 0).map_smul r x
  invFun := (DerivedCategory.singleFunctor C 0).preimage
  left_inv x := (DerivedCategory.singleFunctor C 0).preimage_map x
  right_inv y := (DerivedCategory.singleFunctor C 0).map_preimage y

/-- `singleFunctorHomLinearEquiv` sends `a` to its image under the single functor in degree
zero. -/
@[simp]
theorem singleFunctorHomLinearEquiv_apply (A B : C) (a : A ⟶ B) :
    singleFunctorHomLinearEquiv k A B a = (DerivedCategory.singleFunctor C 0).map a :=
  rfl

end Single

/-! ### The pure-tensor law, and `himage` at the standard model from it -/

section Specialization

variable (X Y : Over (Spec (.of k)))

/-- **The pure-tensor law of the degree-zero Künneth chain**: under the `k`-linear
identifications `Hom(N, N') ≃ H⁰RΓ(R𝓗om(N, N'))` of [Stacks, Tag 08DK]
(`AlgebraicGeometry.homLinearEquivDegreeZeroSections`) on `X`, `Y` and `W = X ×_k Y`, the class
of `φ ⊠ ψ` is the image of `[φ] ⊗ [ψ]` under the degree-zero Künneth map followed by `H⁰RΓ` of
`boxSheafHomMap`. -/
def DegreeZeroPureTensorLaw : Prop :=
  ∀ (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules)
    (φ : K ⟶ K') (ψ : M ⟶ M'),
    homLinearEquivDegreeZeroSections k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)) _ _
        (tensorMap (pullback X.hom Y.hom).toRingedSpace
          ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
          ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
      (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom
        ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace K K')
            (sheafHomObj Y.left.toRingedSpace M M')).hom
          (homLinearEquivDegreeZeroSections k X K K' φ ⊗ₜ
            homLinearEquivDegreeZeroSections k Y M M' ψ))


/-! ### The pure-tensor law from its unit case -/

/-- **Naturality of `boxSheafHomMap` in its two targets** ((N2) of the reduction): postcomposing
with `φ` and `ψ` before the comparison is postcomposing with `φ ⊠ ψ` after it. -/
def BoxSheafHomMapTargetNaturality : Prop :=
  ∀ (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules)
    (φ : K ⟶ K') (ψ : M ⟶ M'),
    tensorMap (pullback X.hom Y.hom).toRingedSpace
        ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map
          ((sheafHomOutOf k X K).map φ))
        ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map
          ((sheafHomOutOf k Y M).map ψ)) ≫
      boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M' =
    boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K M M ≫
      (sheafHomOutOf k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)).map
        (tensorMap (pullback X.hom Y.hom).toRingedSpace
          ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
          ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ))

/-- **(N2) holds**: `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap_naturality_target` at the
fibre product `X ×_k Y`. -/
theorem boxSheafHomMapTargetNaturality : BoxSheafHomMapTargetNaturality k X Y :=
  fun K K' M M' φ ψ =>
    Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap_naturality_target
      (pullback.fst X.hom Y.hom).toLRSHom.toShHom (pullback.snd X.hom Y.hom).toLRSHom.toShHom
      K M (K'' := K') (M'' := M') φ ψ

/-- **The unit case of the pure-tensor law**: the class of the identity of `K ⊠ M` is the image
of `[𝟙_K] ⊗ [𝟙_M]`. -/
def DegreeZeroPureTensorUnitLaw : Prop :=
  ∀ (K : DerivedCategory X.left.Modules) (M : DerivedCategory Y.left.Modules),
    homLinearEquivDegreeZeroSections k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)) _ _
        (𝟙 (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)) =
      (degreeZeroBoxSheafHomMap k X.hom Y.hom K K M M).hom
        ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace K K)
            (sheafHomObj Y.left.toRingedSpace M M)).hom
          (homLinearEquivDegreeZeroSections k X K K (𝟙 K) ⊗ₜ
            homLinearEquivDegreeZeroSections k Y M M (𝟙 M)))

/-- **The pure-tensor law follows from its unit case** and the naturality of `boxSheafHomMap`
in its targets, by the naturality of [Stacks, Tag 08DK] in the target
(`AlgebraicGeometry.homLinearEquivDegreeZeroSections_comp`) and of the degree-zero Künneth map
(`AlgebraicGeometry.degreeZeroKunnethMap_naturality`). -/
theorem degreeZeroPureTensorLaw_of_unitLaw (hN2 : BoxSheafHomMapTargetNaturality k X Y)
    (hU : DegreeZeroPureTensorUnitLaw k X Y) : DegreeZeroPureTensorLaw k X Y := by
  intro K K' M M' φ ψ
  let Φ := sectionsOverBase (pullback.fst X.hom Y.hom ≫ X.hom).toLRSHom.toShHom ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0
  let T := tensorMap (pullback X.hom Y.hom).toRingedSpace
    ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
    ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)
  have eW := homLinearEquivDegreeZeroSections_eq_map k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
    (N := boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
    (N' := boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M') T
  have eX := homLinearEquivDegreeZeroSections_eq_map k X φ
  have eY := homLinearEquivDegreeZeroSections_eq_map k Y ψ
  have hA := Φ.map_comp (tensorMap (pullback X.hom Y.hom).toRingedSpace
        ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map
          ((sheafHomOutOf k X K).map φ))
        ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map
          ((sheafHomOutOf k Y M).map ψ)))
    (boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M')
  have hB := Φ.map_comp (boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K M M)
    ((sheafHomOutOf k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)).map T)
  have e2 := hA.symm.trans ((congrArg Φ.map (hN2 K K' M M' φ ψ)).trans hB)
  have h1 := ConcreteCategory.congr_hom
    (degreeZeroKunnethMap_naturality k X.hom Y.hom ((sheafHomOutOf k X K).map φ)
      ((sheafHomOutOf k Y M).map ψ))
    (homLinearEquivDegreeZeroSections k X K K (𝟙 K) ⊗ₜ
      homLinearEquivDegreeZeroSections k Y M M (𝟙 M))
  exact eW.trans ((congrArg _ (hU K M)).trans ((ConcreteCategory.congr_hom e2 _).symm.trans
    (congrArg (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom (h1.symm.trans
      (congrArg₂ (fun a b => (degreeZeroKunnethMap k X.hom Y.hom
        (sheafHomObj X.left.toRingedSpace K K')
        (sheafHomObj Y.left.toRingedSpace M M')).hom (a ⊗ₜ b)) eX.symm eY.symm)))))


/-- The transpose is additive. -/
theorem homTranspose_add (V : Over (Spec (.of k))) (N N' : DerivedCategory V.left.Modules)
    (a b : N ⟶ N') :
    homTranspose k V N N' (a + b) = homTranspose k V N N' a + homTranspose k V N N' b := by
  simp only [homTranspose, map_add]

/-- The transpose is injective. -/
theorem homTranspose_injective (V : Over (Spec (.of k))) (N N' : DerivedCategory V.left.Modules) :
    Function.Injective (homTranspose k V N N') := fun a b h => by
  rw [← homTranspose_spec k V N N' a, ← homTranspose_spec k V N N' b, h]

/-- `χ ↦ cls(v ≫ t_χ)` for a fixed endomorphism `v` of `𝒪_V`, additively. -/
def transposeClassHom (V : Over (Spec (.of k))) (N N' : DerivedCategory V.left.Modules)
    (v : structureSheafObj k V ⟶ structureSheafObj k V) :
    (N ⟶ N') →+ degreeZeroSectionsField k V.hom (derivedSheafHomObj k V N N') :=
  AddMonoidHom.mk' (fun χ => degreeZeroClassAddEquiv k V _ (v ≫ homTranspose k V N N' χ))
    fun a b => by rw [homTranspose_add, Preadditive.comp_add, map_add]

/-- `transposeClassHom v` sends `χ` to the class of `v ≫ t_χ`. -/
theorem transposeClassHom_apply (V : Over (Spec (.of k))) (N N' : DerivedCategory V.left.Modules)
    (v : structureSheafObj k V ⟶ structureSheafObj k V) (χ : N ⟶ N') :
    transposeClassHom k V N N' v χ = degreeZeroClassAddEquiv k V _ (v ≫ homTranspose k V N N' χ) :=
  rfl

/-- `transposeClassHom v` is injective when `v` is an isomorphism. -/
theorem transposeClassHom_injective (V : Over (Spec (.of k)))
    (N N' : DerivedCategory V.left.Modules)
    (v : structureSheafObj k V ⟶ structureSheafObj k V) [IsIso v] :
    Function.Injective (transposeClassHom k V N N' v) := fun a b hab =>
  homTranspose_injective k V N N' (a₁ := a) (a₂ := b)
    ((cancel_epi v).1 ((degreeZeroClassAddEquiv k V _).injective hab))

/-! ### The relaxed pure-tensor law: classes of transposes -/

/-- **The pure-tensor law on transposes** ((U4)): for some isomorphism
`ε : 𝒪_W ≅ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` depending only on the objects, the transpose
`𝒪_W ⟶ R𝓗om(K ⊠ M, K' ⊠ M')` of `φ ⊠ ψ` is `ε` followed by `Lp^*t_φ ⊗ Lq^*t_ψ` and the comparison
`boxSheafHomMap`, where `t` is `AlgebraicGeometry.homTranspose`. -/
def DegreeZeroPureTensorTransposeLaw : Prop :=
  ∀ (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules),
    ∃ ε : structureSheafObj k (fibreProductOver k X Y) ≅
        boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y),
      ∀ (φ : K ⟶ K') (ψ : M ⟶ M'),
        homTranspose k (fibreProductOver k X Y)
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')
            (tensorMap (pullback X.hom Y.hom).toRingedSpace
              ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
              ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
          ε.hom ≫ boxDerivedMap k X Y (homTranspose k X K K' φ) (homTranspose k Y M M' ψ) ≫
            boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M'

/-- **From the transpose law, an injective reading of `Hom(K ⊠ M, K' ⊠ M')` in
`H⁰RΓ(W, R𝓗om(K ⊠ M, K' ⊠ M'))` under which `φ ⊠ ψ` is the image of `e_X φ ⊗ e_Y ψ`**: it is
`χ ↦ cls((u ≫ ε⁻¹) ≫ t_χ)`, injective since the unit `u` of the degree-zero Künneth map on
classes is invertible (`AlgebraicGeometry.isIso_degreeZeroKunnethUnit`). -/
theorem exists_injective_degreeZeroPureTensor
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (hT : DegreeZeroPureTensorTransposeLaw k X Y)
    (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules) :
    ∃ D : (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M ⟶
        boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M') →+
        degreeZeroSectionsField k (pullback.fst X.hom Y.hom ≫ X.hom)
          (sheafHomObj (pullback X.hom Y.hom).toRingedSpace
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')),
      Function.Injective D ∧ ∀ (φ : K ⟶ K') (ψ : M ⟶ M'),
        D (tensorMap (pullback X.hom Y.hom).toRingedSpace
            ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
            ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
          (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom
            ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace K K')
                (sheafHomObj Y.left.toRingedSpace M M')).hom
              (homLinearEquivDegreeZeroSections k X K K' φ ⊗ₜ
                homLinearEquivDegreeZeroSections k Y M M' ψ)) := by
  obtain ⟨ε, hε⟩ := hT K K' M M'
  have := isIso_degreeZeroKunnethUnit k X Y
  let v := degreeZeroKunnethUnit k X Y ≫ ε.inv
  let cls := degreeZeroClassAddEquiv k (fibreProductOver k X Y)
    (derivedSheafHomObj k (fibreProductOver k X Y)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M'))
  refine ⟨transposeClassHom k (fibreProductOver k X Y) _ _ v,
    transposeClassHom_injective k _ _ _ v, ?_⟩
  · intro φ ψ
    have hmor : v ≫ homTranspose k (fibreProductOver k X Y) _ _
          (tensorMap (pullback X.hom Y.hom).toRingedSpace
            ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
            ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
        (degreeZeroKunnethUnit k X Y ≫
          boxDerivedMap k X Y (homTranspose k X K K' φ) (homTranspose k Y M M' ψ)) ≫
          boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M' := by
      rw [hε φ ψ]
      simp only [v, Category.assoc, Iso.inv_hom_id_assoc]
      exact (Category.assoc _ _ _).symm
    have hU1 := degreeZeroClassAddEquiv_comp k (fibreProductOver k X Y)
      (degreeZeroKunnethUnit k X Y ≫
        boxDerivedMap k X Y (homTranspose k X K K' φ) (homTranspose k Y M M' ψ))
      (boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M')
    have hU2 := degreeZeroKunnethMap_classes k X Y (homTranspose k X K K' φ)
      (homTranspose k Y M M' ψ)
    have h1 := homLinearEquivDegreeZeroSections_eq_class k X K K' φ
    have h2 := homLinearEquivDegreeZeroSections_eq_class k Y M M' ψ
    refine (transposeClassHom_apply k (fibreProductOver k X Y) _ _ v _).trans ?_
    exact (congrArg cls hmor).trans (hU1.trans
      (congrArg (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom (hU2.symm.trans
        (congrArg₂ (fun a b => (degreeZeroKunnethMap k X.hom Y.hom
          (sheafHomObj X.left.toRingedSpace K K') (sheafHomObj Y.left.toRingedSpace M M')).hom
            (a ⊗ₜ b)) h1.symm h2.symm))))

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

/-- The assembly `isTensorPairing_of_degreeZeroKunneth` at the terms `ℰᵢ ⊠ F(𝒢ᵢ)` of Tag 0G0A,
given an injective additive reading `D` under which `φ ⊠ ψ` is the image of `e_X φ ⊗ e_Y ψ`. -/
private theorem isTensorPairing_transformedImagePairingStd_of_injective
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (R : DiagonalResolution X.hom)
    (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] (hff : F.FullyFaithful)
    (i j : ℕ)
    (D : (derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd i)
        (R.secondFactorImageStd F i) ⟶
        derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd j)
          (R.secondFactorImageStd F j)) →+
      degreeZeroSectionsField k (pullback.fst X.hom Y.hom ≫ X.hom)
        (sheafHomObj (pullback X.hom Y.hom).toRingedSpace
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom
            ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i))
            (R.secondFactorImageStd F i))
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom
            ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
            (R.secondFactorImageStd F j))))
    (hD : Function.Injective D)
    (hlaw : ∀ (φ : (DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i) ⟶
          (DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
        (ψ : R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j),
      D (tensorMap (pullback X.hom Y.hom).toRingedSpace
          ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
          ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
        (degreeZeroBoxSheafHomMap k X.hom Y.hom _ _ _ _).hom
          ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace _ _)
              (sheafHomObj Y.left.toRingedSpace _ _)).hom
            (homLinearEquivDegreeZeroSections k X _ _ φ ⊗ₜ
              homLinearEquivDegreeZeroSections k Y _ _ ψ))) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    IsTensorPairing k (R.left i ⟶ R.left j)
      (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
      (R.transformedImagePairingStd Y.hom F i j) := by
  let : Linear k X.left.Modules := modulesLinear k X
  let : Linear k Y.left.Modules := modulesLinear k Y
  refine isTensorPairing_of_degreeZeroKunneth k X.hom Y.hom
    (P := derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd i) (R.secondFactorImageStd F i) ⟶
      derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd j) (R.secondFactorImageStd F j))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
    (R.secondFactorImageStd F i) (R.secondFactorImageStd F j)
    (isPerfect_singleFunctor_of_isFiniteLocallyFree_std _ _ (R.isFiniteLocallyFree_left i))
    (R.isPerfect_secondFactorImageStd F i)
    (R.isQCohAll_derivedSheafHom_left i j)
    (R.isQCohAll_derivedSheafHom_secondFactorImageStd F i j)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_left k i j p hp)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd F hff
      Y.hom i j p hp)
    (singleFunctorHomLinearEquiv k _ _ ≪≫ₗ homLinearEquivDegreeZeroSections k X _ _)
    (homLinearEquivDegreeZeroSections k Y _ _)
    D hD _ fun a c => ?_
  rw [R.transformedImagePairingStd_of_eq_tensorMap]
  exact hlaw _ _

/-- **The Künneth input `himage` of Tag 0G0A at the standard model, from the pure-tensor law.** -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_law
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (hlaw : DegreeZeroPureTensorLaw k X Y) (R : DiagonalResolution X.hom)
    (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] (hff : F.FullyFaithful)
    (i j : ℕ) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    IsTensorPairing k (R.left i ⟶ R.left j)
      (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
      (R.transformedImagePairingStd Y.hom F i j) :=
  isTensorPairing_transformedImagePairingStd_of_injective k X Y R F hff i j
    (homLinearEquivDegreeZeroSections k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
      _ _).toAddMonoidHom
    (homLinearEquivDegreeZeroSections k (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)) _ _).injective
    fun _ _ => hlaw _ _ _ _ _ _

/-- **The Künneth input `himage` of Tag 0G0A at the standard model, from the transpose law.** -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_transposeLaw'
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (hT : DegreeZeroPureTensorTransposeLaw k X Y) (R : DiagonalResolution X.hom)
    (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] (hff : F.FullyFaithful)
    (i j : ℕ) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    IsTensorPairing k (R.left i ⟶ R.left j)
      (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
      (R.transformedImagePairingStd Y.hom F i j) := by
  obtain ⟨D, hD, hDlaw⟩ := exists_injective_degreeZeroPureTensor k X Y hT
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
    (R.secondFactorImageStd F i) (R.secondFactorImageStd F j)
  exact isTensorPairing_transformedImagePairingStd_of_injective k X Y R F hff i j D hD hDlaw

end Specialization

section Situation

attribute [-instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

variable (X Y : Over (Spec (.of k)))

/-- **`himage` of Tag 0G0A at the standard model, at Situation 0G08's hypotheses**, given the
pure-tensor law: `k` a field, `X` and `Y` smooth and proper over `k`, and `F` a `k`-linear, exact,
fully faithful functor between the perfect derived categories (smoothness and `k`-linearity of `F`
are not used). -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_situation_of_law
    [Smooth X.hom] [Smooth Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hlaw : DegreeZeroPureTensorLaw k X Y) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom) (i j : ℕ),
        IsTensorPairing k (R.left i ⟶ R.left j)
          (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
          (R.transformedImagePairingStd Y.hom F i j) := by
  intro F _ _ _ hff R i j
  exact R.isTensorPairing_transformedImagePairingStd_of_law k X Y hlaw F hff.some i j

/-- **`himage` of Tag 0G0A at the standard model, at Situation 0G08's hypotheses, from the unit
case of the pure-tensor law alone**: the target naturality of `boxSheafHomMap` is
`AlgebraicGeometry.boxSheafHomMapTargetNaturality`. -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_unitLaw
    [Smooth X.hom] [Smooth Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hU : DegreeZeroPureTensorUnitLaw k X Y) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom) (i j : ℕ),
        IsTensorPairing k (R.left i ⟶ R.left j)
          (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
          (R.transformedImagePairingStd Y.hom F i j) :=
  DiagonalResolution.isTensorPairing_transformedImagePairingStd_situation_of_law k X Y
    (degreeZeroPureTensorLaw_of_unitLaw k X Y (boxSheafHomMapTargetNaturality k X Y) hU)

/-- **`himage` of Tag 0G0A at the standard model, at Situation 0G08's hypotheses, from the
transpose law (U4) alone.** This is the statement pinned for
`AlgebraicGeometry.exists_kunnethComplex_of_imagePairingStd`, with
`AlgebraicGeometry.DegreeZeroPureTensorTransposeLaw` as its only input. -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_transposeLaw
    [Smooth X.hom] [Smooth Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hT : DegreeZeroPureTensorTransposeLaw k X Y) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom) (i j : ℕ),
        IsTensorPairing k (R.left i ⟶ R.left j)
          (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
          (R.transformedImagePairingStd Y.hom F i j) := by
  intro F _ _ _ hff R i j
  exact R.isTensorPairing_transformedImagePairingStd_of_transposeLaw' k X Y hT F hff.some i j

end Situation

end AlgebraicGeometry
