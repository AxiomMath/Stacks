module

public import StacksFrontier.AlgebraicGeometry.ProjMapCardUnit.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Basic

/-!
# Comparison maps on twists through the pullback--pushforward adjunction

Let `r : U(ψ) ⟶ Proj 𝒜` be the canonical morphism attached to a graded ring map `ψ : 𝒜 →+*ᵍ ℬ`.
A family of comparison maps `r^*𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)|_{U(ψ)}` on all twists has an
adjoint transpose `𝒪_{Proj 𝒜}(n) ⟶ r_*(𝒪_{Proj ℬ}(n)|_{U(ψ)})`. This file expresses the
multiplication law and the condition at `⊤` of the uniqueness clause of Tag 01MY, for an
arbitrary family, as pointwise statements about the values of the adjoint transpose.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.TwistFamily`: the type of families of comparison
  maps on twists.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.adjointFamily`: the adjoint transpose of a family
  of comparison maps, a morphism `𝒪_{Proj 𝒜}(n) ⟶ r_* (𝒪_{Proj ℬ}(n)|_{U(ψ)})`.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.eq_twistMap_of_adjointFamily_eq`: a family whose
  adjoint transpose is the adjoint form of `θ` *is* `θ`.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.adjointFamily_pullbackUnit`: the family evaluated
  on a pullback-unit image is its adjoint transpose followed by the identification of
  restriction with pullback.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.adjointFamily_absoluteTwistProduct`: **the
  multiplication law, on sections.** The adjoint transpose on the canonical product of two
  honest sections is the canonical product of their images.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.adjointFamily_mul_val`: the same, pointwise: the
  value at a point of the image open is the product of the two values there.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.adjointFamily_degreeSection_val`: **condition
  (1), pointwise.** The adjoint transpose carries the global section attached to a homogeneous
  `a` of degree `k` to the family whose value everywhere is `ψ a / 1`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.TwistTensor Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjMapUniqueTwist

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The type of families of comparison maps `r^*𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)|_{U(ψ)}` on all
twists, for the canonical morphism `r : U(ψ) ⟶ Proj 𝒜`. -/
public abbrev TwistFamily (ψ : 𝒜 →+*ᵍ ℬ) : Type u :=
  ∀ n : ℤ, (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 n) ⟶
    (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)

variable (ψ : 𝒜 →+*ᵍ ℬ)

/-- **The adjoint transpose of a family of comparison maps on twists**: the morphism
`𝒪_{Proj 𝒜}(n) ⟶ r_*(𝒪_{Proj ℬ}(n)|_{U(ψ)})` corresponding under the pullback--pushforward
adjunction to `tw n` followed by the identification of pullback with restriction. -/
public def adjointFamily (tw : TwistFamily 𝒜 ℬ ψ) (n : ℤ) :
    twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _)
    (tw n ≫ (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).inv.app
      (twistingSheaf ℬ n))

variable {𝒜 ℬ ψ}

/-- A family is recovered from its adjoint transpose: transpose back and compose with the
identification of restriction with pullback. -/
public theorem eq_comp_restrictFunctorIsoPullback (tw : TwistFamily 𝒜 ℬ ψ) (n : ℤ) :
    tw n = ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
        (adjointFamily 𝒜 ℬ ψ tw n) ≫
      (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n) := by
  simp only [adjointFamily, Equiv.symm_apply_apply, Category.assoc]
  exact (Category.comp_id _).symm.trans (congrArg (tw n ≫ ·) (Iso.inv_hom_id_app _ _).symm)

/-- **A family whose adjoint transpose is the adjoint form of `θ` is `θ`.** -/
public theorem eq_twistMap_of_adjointFamily_eq (tw : TwistFamily 𝒜 ℬ ψ) (n : ℤ)
    (h : adjointFamily 𝒜 ℬ ψ tw n = twistPushforwardMap 𝒜 ℬ ψ n) :
    tw n = twistMap 𝒜 ℬ ψ n :=
  (eq_comp_restrictFunctorIsoPullback tw n).trans (by rw [h]; rfl)

/-- The unit of the pullback--pushforward adjunction followed by the pushforward of a family is
its adjoint transpose followed by the pushforward of the identification of restriction with
pullback. -/
public theorem unit_comp_map_twistFamily (tw : TwistFamily 𝒜 ℬ ψ) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
        (twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map (tw n) =
    adjointFamily 𝒜 ℬ ψ tw n ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n)) := by
  refine Eq.trans (congrArg (fun k =>
      (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
        (twistingSheaf 𝒜 n) ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map k)
    (eq_comp_restrictFunctorIsoPullback tw n)) ?_
  refine Eq.trans (congrArg (fun k =>
      (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
        (twistingSheaf 𝒜 n) ≫ k)
    (Functor.map_comp (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)) _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun k => k ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
    ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n))) ?_
  exact (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction
    (mapHom 𝒜 ℬ ψ)) _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- Equal morphisms of sheaves of modules take equal values on sections. -/
private theorem hom_app_congr {X : Scheme.{u}} {M N : X.Modules} {φ φ' : M ⟶ N} (h : φ = φ')
    (U : X.Opens) (w : M.val.obj (op U)) :
    Hom.app φ.val (op U) w = Hom.app φ'.val (op U) w :=
  congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) (op U) w) h

/-- **A family evaluated on a pullback-unit image.** The value is the adjoint transpose followed
by the identification of restriction with pullback. -/
public theorem adjointFamily_pullbackUnit (tw : TwistFamily 𝒜 ℬ ψ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (w : (twistingSheaf 𝒜 n).val.obj (op U)) :
    Hom.app (tw n).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (pullbackUnit (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom (twistingSheaf 𝒜 n) (op U) w) =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ n)).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (Hom.app (adjointFamily 𝒜 ℬ ψ tw n).val (op U) w) :=
  hom_app_congr (unit_comp_map_twistFamily tw n) U w

/-- The identification of restriction with pullback is injective on sections. -/
public theorem restrictFunctorIsoPullback_hom_app_injective {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (N : Y.Modules) (V : X.Opens)
    {x y : ((Scheme.Modules.restrictFunctor g).obj N).val.obj (op V)}
    (h : Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V) x =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V) y) :
    x = y := by
  have hcancel : ∀ w : ((Scheme.Modules.restrictFunctor g).obj N).val.obj (op V),
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app N).val (op V)
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V) w) = w :=
    fun w => hom_app_congr (Iso.hom_inv_id_app (Scheme.Modules.restrictFunctorIsoPullback g) N) V w
  exact ((hcancel x).symm.trans (congrArg (Hom.app
    ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app N).val (op V)) h)).trans (hcancel y)

/-- **The multiplication law, on sections.** If the family satisfies the multiplication law
`hmul`, then for honest sections `s` of `𝒪(n)` and `t` of `𝒪(m)` over an open `U` of `Proj 𝒜`,
the adjoint transpose of the family on the `(n + m)`-th twist carries the canonical product of
`s` and `t` to the canonical product of their images. -/
public theorem adjointFamily_absoluteTwistProduct (tw : TwistFamily 𝒜 ℬ ψ)
    (hmul : ∀ n m : ℤ,
      pullbackTwistMultiplication 𝒜 (mapHom 𝒜 ℬ ψ) n m ≫ tw (n + m) =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((mapDomain 𝒜 ℬ
          ψ).toScheme.toRingedSpace)).presheaf, (((mapDomain 𝒜 ℬ
          ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map (((tw n), (tw m)) : (_, _) ⟶ (_, _))) ≫
          pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m)
    (n m : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op U)) (t : (twistingSheaf 𝒜 m).val.obj (op U)) :
    Hom.app (adjointFamily 𝒜 ℬ ψ tw (n + m)).val (op U)
        (absoluteTwistProduct 𝒜 n m U s t) =
      absoluteTwistProduct ℬ n m ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (Hom.app (adjointFamily 𝒜 ℬ ψ tw n).val (op U) s)
        (Hom.app (adjointFamily 𝒜 ℬ ψ tw m).val (op U) t) := by
  refine restrictFunctorIsoPullback_hom_app_injective (mapDomain 𝒜 ℬ ψ).ι
    (twistingSheaf ℬ (n + m)) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) ?_
  refine Eq.trans (adjointFamily_pullbackUnit tw (n + m) U
    (absoluteTwistProduct 𝒜 n m U s t)).symm ?_
  refine Eq.trans (congrArg (Hom.app (tw (n + m)).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (pullbackUnit_naturality (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom
      (twistMultiplicationMap 𝒜 n m) (op U)
      (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((AlgebraicGeometry.Proj 𝒜).toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
            ((AlgebraicGeometry.Proj 𝒜).toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj 𝒜).toRingedSpace).presheaf)
          ((twistingSheaf 𝒜 n)).val ((twistingSheaf 𝒜 m)).val)) (op U) (s ⊗ₜ t))).symm) ?_
  refine Eq.trans (hom_app_congr
    ((Eq.trans (Category.assoc _ _ _).symm (congrArg (fun k => k ≫ tw (n + m))
        (comparison_comp_pullbackTwistMultiplication 𝒜 (mapHom 𝒜 ℬ ψ) n m))).symm.trans
      (congrArg (fun k => (Stacks.PullbackTensorIso.pullbackTensorIso
          (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom).hom.app
            (twistingSheaf 𝒜 n, twistingSheaf 𝒜 m) ≫ k) (hmul n m))) _ _) ?_
  refine Eq.trans (congrArg (fun w => Hom.app
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).presheaf,
        (((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
        (((tw n), (tw m)) : (_, _) ⟶ (_, _))) ≫
        pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m).val
      (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) w)
    (comparison_pullbackUnit_tensorSheafUnit (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom
      (twistingSheaf 𝒜 n) (twistingSheaf 𝒜 m) U s t)) ?_
  refine Eq.trans (congrArg (Hom.app (pullbackTwistMultiplication ℬ
      (mapDomain 𝒜 ℬ ψ).ι n m).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (tensorSheaf_map_unit_tmul (mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace (tw n) (tw m)
      (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) _ _)) ?_
  refine Eq.trans (congrArg₂ (fun a b => Hom.app (pullbackTwistMultiplication ℬ
        (mapDomain 𝒜 ℬ ψ).ι n m).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
      (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
            ((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := ((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace).presheaf)
          (((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))).val
          (((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ m))).val))
        (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) (a ⊗ₜ b)))
    (adjointFamily_pullbackUnit tw n U s) (adjointFamily_pullbackUnit tw m U t)) ?_
  refine Eq.trans (congrArg (Hom.app ((Scheme.Modules.pullback
      (mapDomain 𝒜 ℬ ψ).ι).map (twistMultiplicationMap ℬ n m)).val
      (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (restrictFunctorIsoPullback_tensorSheafUnit_eq (mapDomain 𝒜 ℬ ψ).ι
      (twistingSheaf ℬ n) (twistingSheaf ℬ m) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)
      (Hom.app (adjointFamily 𝒜 ℬ ψ tw n).val (op U) s)
      (Hom.app (adjointFamily 𝒜 ℬ ψ tw m).val (op U) t))) ?_
  exact (restrictFunctorIsoPullback_hom_app_naturality (mapDomain 𝒜 ℬ ψ).ι
    (twistMultiplicationMap ℬ n m) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) _).symm

/-- **The multiplication law, pointwise.** If the family satisfies the multiplication law `hmul`,
then at every point of the image of `r ⁻¹ᵁ U` the value of the adjoint transpose on the canonical
product is the product of the two values. -/
public theorem adjointFamily_mul_val (tw : TwistFamily 𝒜 ℬ ψ)
    (hmul : ∀ n m : ℤ,
      pullbackTwistMultiplication 𝒜 (mapHom 𝒜 ℬ ψ) n m ≫ tw (n + m) =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((mapDomain 𝒜 ℬ
          ψ).toScheme.toRingedSpace)).presheaf, (((mapDomain 𝒜 ℬ
          ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map (((tw n), (tw m)) : (_, _) ⟶ (_, _))) ≫
          pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m)
    (n m : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op U)) (t : (twistingSheaf 𝒜 m).val.obj (op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    (Hom.app (adjointFamily 𝒜 ℬ ψ tw (n + m)).val (op U)
        (absoluteTwistProduct 𝒜 n m U s t)).1 z =
      (Hom.app (adjointFamily 𝒜 ℬ ψ tw n).val (op U) s).1 z *
        (Hom.app (adjointFamily 𝒜 ℬ ψ tw m).val (op U) t).1 z :=
  (Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr ℬ
      (adjointFamily_absoluteTwistProduct tw hmul n m U s t) z).trans
    (Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply ℬ n m
      ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
      (Hom.app (adjointFamily 𝒜 ℬ ψ tw n).val (op U) s)
      (Hom.app (adjointFamily 𝒜 ℬ ψ tw m).val (op U) t) z)

/-- **Condition (1), on the adjoint transpose.** If the family carries the unit image of the
global section of `𝒪(k)` attached to each homogeneous `a` of degree `k` to the unit image of the
global section attached to `ψ a` (`hdegree`), then its adjoint transpose carries the global
section attached to `a` to the restriction to `U(ψ)` of the global section attached to `ψ a`. -/
public theorem adjointFamily_degreeSection (tw : TwistFamily 𝒜 ℬ ψ)
    (hdegree : ∀ (k : ℕ) (a : 𝒜 k),
      (tw (k : ℤ)).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
          (twistingSheaf 𝒜 (k : ℤ))).val.app (op ⊤) (degreeSection 𝒜 k a)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
        (twistingSheaf ℬ (k : ℤ))).val.app (op ⊤)
          (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩))
    (k : ℕ) (a : 𝒜 k) :
    Hom.app (adjointFamily 𝒜 ℬ ψ tw (k : ℤ)).val (op ⊤) (degreeSection 𝒜 k a) =
      Hom.app ((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
          (twistingSheaf ℬ (k : ℤ))).val (op ⊤)
        (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩) := by
  refine restrictFunctorIsoPullback_hom_app_injective (mapDomain 𝒜 ℬ ψ).ι
    (twistingSheaf ℬ (k : ℤ)) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ ⊤) ?_
  refine Eq.trans (adjointFamily_pullbackUnit tw (k : ℤ) ⊤ (degreeSection 𝒜 k a)).symm ?_
  refine Eq.trans (hdegree k a) ?_
  exact hom_app_congr (restrictUnit_comp_map_restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι
    (twistingSheaf ℬ (k : ℤ))).symm ⊤ (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩)

/-- **Condition (1), pointwise.** Under the hypothesis `hdegree`, the adjoint transpose carries
the global section attached to a homogeneous `a` of degree `k` to the family whose value at every
point of `U(ψ)` is `ψ a / 1`. -/
public theorem adjointFamily_degreeSection_val (tw : TwistFamily 𝒜 ℬ ψ)
    (hdegree : ∀ (k : ℕ) (a : 𝒜 k),
      (tw (k : ℤ)).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
          (twistingSheaf 𝒜 (k : ℤ))).val.app (op ⊤) (degreeSection 𝒜 k a)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
        (twistingSheaf ℬ (k : ℤ))).val.app (op ⊤)
          (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩))
    (k : ℕ) (a : 𝒜 k)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))) :
    (Hom.app (adjointFamily 𝒜 ℬ ψ tw (k : ℤ)).val (op ⊤) (degreeSection 𝒜 k a)).1 z =
      LocalizedModule.mk ((ψ a : B)) 1 :=
  (Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr ℬ
      (adjointFamily_degreeSection tw hdegree k a) z).trans
    (restrictUnit_degreeSection_val 𝒜 ℬ ψ k ⟨ψ a, ψ.map_mem a.2⟩ z)

end Stacks.AlgebraicGeometry.ProjMapUniqueTwist

end
