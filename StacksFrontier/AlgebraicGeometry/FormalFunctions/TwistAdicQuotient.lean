module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic

/-!
# Twisting by an invertible module commutes with the adic quotients of a base ideal

Let `A` be a commutative ring, `f : X ⟶ Spec A` a scheme over it, `I ⊆ A` an ideal and
`𝓘 = I · 𝒪_X` the ideal sheaf it generates. For an invertible `𝒪_X`-module `ℒ` and an integer
`d` this file identifies

`(ℱ ⊗ ℒ ^⊗ d) / 𝓘 ᵏ (ℱ ⊗ ℒ ^⊗ d) ≅ (ℱ / 𝓘 ᵏ ℱ) ⊗ ℒ ^⊗ d`,

compatibly with the quotient projections and with the exponent-lowering maps of the adic tower,
and deduces the same for the tower's transition kernels `𝓘 ᵏ ℱ / 𝓘 ᵏ⁺¹ ℱ`. This is the step
[Stacks, Tag 0D2M] takes silently when it applies its graded input to the twists `ℱ(d)`: the
subquotients of the `𝔪`-adic filtration of `ℱ(d)` are the twists of those of `ℱ`, because
`ℒ ^⊗ d` is invertible.

## The argument

Nothing here computes a section of a tensor product, and nothing transports a subsheaf along the
tensor equivalence. The whole content is routed through **multiplication by a base scalar**: for
`a ∈ A` the endomorphism `AlgebraicGeometry.baseScalar A (Over.mk f) a` of the identity functor
of `X.Modules`, which on sections is multiplication by the image of `a` in `Γ(X, 𝒪_X)`. Three
facts about it suffice.

* `Stacks.Algebraization.baseSmul_eq_zero_of_idealPowerMultiple_eq_bot`: a module killed by
  `𝓘 ᵏ` is annihilated by every `a ∈ I ᵏ`.
* Conversely `𝓘 ᵏ` is generated, affine-locally, by the restrictions of the images of `I ᵏ`
  (`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_ideal`), so a module annihilated by every
  `a ∈ I ᵏ` is killed by `𝓘 ᵏ`. That is
  `Stacks.Cohomology.FormalFunctions.idealPowerMultiple_eq_bot_of_baseScalar_eq_zero`.
* Tensoring carries multiplication by a scalar to multiplication by the same scalar
  (`Stacks.sheafTensorRight_map_globalSmul`), and so therefore does the quasi-inverse of the
  tensor equivalence, by faithfulness.

Together these say that **annihilation by `𝓘 ᵏ` is preserved by twisting**
(`idealPowerMultiple_map_eq_bot`), and that gives both factorizations needed to compare
the cokernels of the two inclusions into `ℱ ⊗ ℒ ^⊗ d`:

* `(ℱ ⊗ ℒ ^⊗ d)/𝓘 ᵏ(ℱ ⊗ ℒ ^⊗ d)` is killed by `𝓘 ᵏ`, so its projection kills the twist of
  `𝓘 ᵏ ℱ` — after applying the quasi-inverse this is
  `Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot` at `ℱ`;
* `(ℱ/𝓘 ᵏ ℱ) ⊗ ℒ ^⊗ d` is killed by `𝓘 ᵏ`, being the twist of something that is, so the twisted
  projection kills `𝓘 ᵏ(ℱ ⊗ ℒ ^⊗ d)`.

The two descended maps are mutually inverse because the quotient projections are epimorphisms,
and the resulting isomorphism intertwines the exponent-lowering maps for the same reason.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.idealPowerQuotientIsoOfEquivalence` — the comparison
  `e (ℱ/𝓘 ᵏ ℱ) ≅ (e ℱ)/𝓘 ᵏ (e ℱ)` for an autoequivalence `e` of `X.Modules` carrying the base
  scalars to themselves.
* `Stacks.Cohomology.FormalFunctions.transitionKernelIsoOfEquivalence` — the comparison of the
  transition kernels of the two adic towers.
* `Stacks.Cohomology.FormalFunctions.twistTransitionKernelIso` — the same at the twist
  `− ⊗ ℒ ^⊗ d`, which is such an autoequivalence.

## Main results

* `Stacks.Cohomology.FormalFunctions.idealPowerMultiple_eq_bot_of_baseScalar_eq_zero` — a module
  annihilated by every scalar of `I ᵏ` is killed by `𝓘 ᵏ`.
* `Stacks.Cohomology.FormalFunctions.idealPowerMultiple_map_eq_bot` — annihilation by `𝓘 ᵏ` is
  preserved by any endofunctor carrying the base scalars to themselves, the twist and the
  quasi-inverse of the twist included.
* `Stacks.Cohomology.FormalFunctions.map_π_comp_idealPowerQuotientIsoOfEquivalence_hom` and
  `Stacks.Cohomology.FormalFunctions.idealPowerQuotientIsoOfEquivalence_hom_naturality` — the
  comparison is compatible with the quotient projections and intertwines the exponent-lowering
  maps.

## Implementation notes

The twist is `Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor`, the library's
endofunctor `ℱ ↦ ℱ ⊗ ℒ ^⊗ d` with its target already ascribed to the spelling
`SheafOfModules X.ringCatSheaf` that `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` is
stated at, and with the additivity and zero-preservation instances already transported there.
Its being an equivalence is `Stacks.AmpleCohomologicalCriterion.isEquivalence_tensorRight`,
applied by hand because the right-tensor functor
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj _` is a projection out of the tensor
bifunctor and synthesis does not see through it.

Multiplication by a base scalar is `AlgebraicGeometry.baseScalar`, an element of the centre of
`X.Modules`; its naturality in the module is `CategoryTheory.NatTrans.naturality` and is what
turns the counit conjugation into an identity. The `Linear A X.Modules` structure that
`Stacks.Algebraization.baseSmul_eq_zero_of_idealPowerMultiple_eq_bot` is stated with is
`AlgebraicGeometry.modulesLinear`, whose scalar action is that same `baseScalar`; the two are
interchangeable by `Category.comp_id`.

Quasi-coherence of the module appears only through
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot`, which is what makes an adic
quotient `𝓘 ᵏ`-torsion.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.AlgebraicGeometry.RelativeSerreVanishing (twistFunctor)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Algebraization Stacks.Ample

/-! ### Annihilation by a power of a base ideal, read through the base scalars -/

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **A module annihilated by every scalar of `I ᵏ` is killed by `(I · 𝒪_X) ᵏ`.**

This is the converse of `Stacks.Algebraization.baseScalar_mem_idealPowerMultiple`, which the
library had only in the forward direction. Over an affine open the ideal `(I · 𝒪_X) ᵏ` is
generated by the restrictions of the images of `I ᵏ`, so the annihilator of the sections contains
it as soon as it contains each of those generators. -/
public lemma idealPowerMultiple_eq_bot_of_baseScalar_eq_zero (I : Ideal A) (k : ℕ)
    (M : X.Modules)
    (h : ∀ a ∈ I ^ k,
      ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app M : M ⟶ M) = (0 : M ⟶ M)) :
    idealPowerMultiple (baseIdealSheaf A I f) k M = ⊥ := by
  refine Stacks.Algebraization.idealPowerMultiple_eq_bot_of_affine_sections_annihilated
    fun U r hr x => ?_
  have hle : (baseIdealSheaf A I f).ideal U ^ k ≤ Module.annihilator Γ(X, U) Γ(M, U) := by
    rw [baseIdealSheaf_ideal, baseIdeal, Ideal.map_map, ← Ideal.map_pow,
      Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.2 (Module.mem_annihilator.2 fun y => ?_)
    have h0 : ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app M).val.app (op U.1) y = 0 := by
      rw [h a ha]; rfl
    exact h0
  exact Module.mem_annihilator.1 (hle hr) x

/-- **A base scalar from `I ᵏ` annihilates a module killed by `(I · 𝒪_X) ᵏ`**, in the
`AlgebraicGeometry.baseScalar` spelling: this is
`Stacks.Algebraization.baseSmul_eq_zero_of_idealPowerMultiple_eq_bot`, whose `Linear A X.Modules`
structure `AlgebraicGeometry.modulesLinear` acts by that very endomorphism. -/
public lemma baseScalar_app_eq_zero_of_idealPowerMultiple_eq_bot (I : Ideal A) (k : ℕ)
    (M : X.Modules) {a : A} (ha : a ∈ I ^ k)
    (hM : idealPowerMultiple (baseIdealSheaf A I f) k M = ⊥) :
    ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app M : M ⟶ M) = (0 : M ⟶ M) := by
  let : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
  exact (Category.comp_id _).symm.trans
    (Stacks.Algebraization.baseSmul_eq_zero_of_idealPowerMultiple_eq_bot A I f M k ha hM)

/-- **Annihilation by `(I · 𝒪_X) ᵏ` passes along any endofunctor of `X.Modules` that preserves
the zero morphism and multiplication by base scalars.** -/
public lemma idealPowerMultiple_map_eq_bot (I : Ideal A) (k : ℕ) (G : X.Modules ⥤ X.Modules)
    (hzero : ∀ {P Q : X.Modules}, G.map (0 : P ⟶ Q) = (0 : G.obj P ⟶ G.obj Q))
    (hG : ∀ (a : A) (N : X.Modules),
      G.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (G.obj N) : G.obj N ⟶ G.obj N))
    (M : X.Modules) (hM : idealPowerMultiple (baseIdealSheaf A I f) k M = ⊥) :
    idealPowerMultiple (baseIdealSheaf A I f) k (G.obj M) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_baseScalar_eq_zero A f I k _ fun a ha => ?_
  rw [← hG a M, baseScalar_app_eq_zero_of_idealPowerMultiple_eq_bot A f I k M ha hM, hzero]

/-- A morphism in the image of the quasi-inverse is determined by its image under the
equivalence, conjugated by the counit. -/
private lemma inverse_map_eq_of_functor_map_eq (e : X.Modules ≌ X.Modules) {P Q : X.Modules}
    (g : P ⟶ Q) (g' : e.inverse.obj P ⟶ e.inverse.obj Q)
    (hg : e.functor.map g' = e.counit.app P ≫ g ≫ e.counitInv.app Q) :
    e.inverse.map g = g' :=
  e.functor.map_injective ((e.fun_inv_map P Q g).trans hg.symm)

/-- **The quasi-inverse of an autoequivalence preserves the zero morphism** as soon as the
equivalence does: the equivalence is faithful. -/
private lemma inverse_map_zero (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    {P Q : X.Modules} :
    e.inverse.map (0 : P ⟶ Q) = (0 : e.inverse.obj P ⟶ e.inverse.obj Q) :=
  inverse_map_eq_of_functor_map_eq e _ _ (by rw [hz, zero_comp, comp_zero])

/-- **The quasi-inverse of an autoequivalence carrying the base scalars to themselves does so
too.** Multiplication by a base scalar is natural in the module, so its conjugate by the counit
is itself, and the equivalence is faithful. -/
private lemma inverse_map_baseScalar (e : X.Modules ≌ X.Modules)
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (a : A) (Y : X.Modules) :
    e.inverse.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app Y : Y ⟶ Y) =
      ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.inverse.obj Y) :
        e.inverse.obj Y ⟶ e.inverse.obj Y) :=
  inverse_map_eq_of_functor_map_eq e _ _ <| by
    have hnat := (AlgebraicGeometry.baseScalar A (Over.mk f) a).naturality (e.counit.app Y)
    refine (h a _).trans ((Eq.trans ?_ (Category.assoc _ _ _)))
    refine Eq.trans ?_ (congrArg (· ≫ e.counitInv.app Y) hnat).symm
    exact ((Category.assoc _ _ _).trans ((congrArg _ (e.counitIso_hom_inv_id_app Y)).trans
      (Category.comp_id _))).symm

/-! ### The adic quotients along an autoequivalence -/

section Equivalence

/-- The image of `e (𝓘 ᵏ ℱ)` in `e ℱ` is killed by the projection onto `(e ℱ) / 𝓘 ᵏ (e ℱ)`.

Applying the quasi-inverse turns the claim into the statement that `𝓘 ᵏ ℱ` is killed by a
morphism whose target is annihilated by `𝓘 ᵏ`, and that is
`Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot`. The target is annihilated
because `(e ℱ) / 𝓘 ᵏ (e ℱ)` is and the quasi-inverse preserves annihilation. -/
public lemma map_ι_comp_π_eq_zero_of_equivalence (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) (k : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (hqc : (e.functor.obj M).IsQuasicoherent) :
    e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι ≫
        cokernel.π (C := X.Modules)
          (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι = 0 := by
  have hbot : idealPowerMultiple (baseIdealSheaf A I f) k
      (e.inverse.obj (idealPowerQuotient (baseIdealSheaf A I f) k (e.functor.obj M))) = ⊥ :=
    idealPowerMultiple_map_eq_bot A f I k e.inverse (fun {_ _} => inverse_map_zero e hz)
      (fun a Y => inverse_map_baseScalar A f e h a Y) _
      (@idealPowerMultiple_idealPowerQuotient_eq_bot X (baseIdealSheaf A I f) k _ hqc)
  have hzero : ((idealPowerMultiple (baseIdealSheaf A I f) k M).ι :
        ((idealPowerMultiple (baseIdealSheaf A I f) k M).toSheafOfModules : X.Modules) ⟶ M) ≫
      ((e.unit.app M ≫ e.inverse.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)) : M ⟶ _) =
      (0 : ((idealPowerMultiple (baseIdealSheaf A I f) k M).toSheafOfModules : X.Modules) ⟶ _) :=
    Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot (baseIdealSheaf A I f) k _ hbot
  have hzero' : (((idealPowerMultiple (baseIdealSheaf A I f) k M).ι :
        ((idealPowerMultiple (baseIdealSheaf A I f) k M).toSheafOfModules : X.Modules) ⟶ M) ≫
      e.unit.app M) ≫ e.inverse.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι) =
      (0 : ((idealPowerMultiple (baseIdealSheaf A I f) k M).toSheafOfModules : X.Modules) ⟶ _) :=
    (Category.assoc _ _ _).trans hzero
  have h1 := Equivalence.inv_fun_map e _ _
    ((idealPowerMultiple (baseIdealSheaf A I f) k M).ι :
      ((idealPowerMultiple (baseIdealSheaf A I f) k M).toSheafOfModules : X.Modules) ⟶ M)
  refine e.inverse.map_injective (((e.inverse.map_comp _ _).trans
    ((congrArg (fun g => g ≫ e.inverse.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => e.unitInv.app _ ≫ g) hzero').trans comp_zero)))).trans
    (inverse_map_zero e hz).symm)

/-- `𝓘 ᵏ` annihilates the cokernel of `e` applied to the inclusion `𝓘 ᵏ ℱ ⟶ ℱ`: that cokernel is
`e (ℱ / 𝓘 ᵏ ℱ)`, and `e` preserves annihilation. -/
public lemma idealPowerMultiple_cokernel_map_ι_eq_bot (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) (k : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    idealPowerMultiple (baseIdealSheaf A I f) k
      (cokernel (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι)) = ⊥ :=
  Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso (baseIdealSheaf A I f)
    (PreservesCokernel.iso e.functor
      (idealPowerMultiple (baseIdealSheaf A I f) k M).ι).symm k
    (idealPowerMultiple_map_eq_bot A f I k e.functor hz h _
      (idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdealSheaf A I f) k M))

/-- The subsheaf `𝓘 ᵏ (e ℱ)` is killed by the projection onto the cokernel of `e` applied to the
inclusion `𝓘 ᵏ ℱ ⟶ ℱ`. -/
public lemma ι_comp_cokernel_π_map_ι_eq_zero (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) (k : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι :
        ((idealPowerMultiple (baseIdealSheaf A I f) k
          (e.functor.obj M)).toSheafOfModules : X.Modules) ⟶ _) ≫
        cokernel.π (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) =
      (0 : ((idealPowerMultiple (baseIdealSheaf A I f) k
        (e.functor.obj M)).toSheafOfModules : X.Modules) ⟶ _) :=
  Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot (baseIdealSheaf A I f) k _
    (idealPowerMultiple_cokernel_map_ι_eq_bot A f e hz h I k M)

/-- **The comparison `e (ℱ / 𝓘 ᵏ ℱ) ≅ (e ℱ) / 𝓘 ᵏ (e ℱ)`.**

Both are cokernels of a subobject of `e ℱ` — the first because `e` preserves cokernels — and
each subobject is killed by the other's projection, so the two cokernel descents are mutually
inverse. -/
public def idealPowerQuotientIsoOfEquivalence (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) (k : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (hqc : (e.functor.obj M).IsQuasicoherent) :
    e.functor.obj (idealPowerQuotient (baseIdealSheaf A I f) k M) ≅
      idealPowerQuotient (baseIdealSheaf A I f) k (e.functor.obj M) :=
  (PreservesCokernel.iso e.functor (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) ≪≫
    { hom := cokernel.desc _ (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)
        (map_ι_comp_π_eq_zero_of_equivalence A f e hz h I k M hqc)
      inv := cokernel.desc _ (cokernel.π
        (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι))
        (ι_comp_cokernel_π_map_ι_eq_zero A f e hz h I k M)
      hom_inv_id := by
        have step1 : cokernel.π (C := X.Modules)
              (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι ≫
            cokernel.desc _ (cokernel.π
              (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι))
              (ι_comp_cokernel_π_map_ι_eq_zero A f e hz h I k M) =
            cokernel.π (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) :=
          cokernel.π_desc _ _ _
        refine (cancel_epi (cokernel.π
          (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι))).1 ?_
        simp [step1]
      inv_hom_id := by
        have step1 : cokernel.π (C := X.Modules)
              (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι ≫
            cokernel.desc _ (cokernel.π
              (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι))
              (ι_comp_cokernel_π_map_ι_eq_zero A f e hz h I k M) =
            cokernel.π (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) :=
          cokernel.π_desc _ _ _
        have step2 : cokernel.π
              (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) ≫
            cokernel.desc _ (cokernel.π (C := X.Modules)
              (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)
              (map_ι_comp_π_eq_zero_of_equivalence A f e hz h I k M hqc) =
            cokernel.π (C := X.Modules)
              (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι :=
          cokernel.π_desc _ _ _
        refine (cancel_epi (cokernel.π (C := X.Modules)
          (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)).1
          (Eq.trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun g => g ≫ cokernel.desc
                (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι)
                (cokernel.π (C := X.Modules)
                  (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι)
                (map_ι_comp_π_eq_zero_of_equivalence A f e hz h I k M hqc)) step1).trans step2))
            (Category.comp_id _).symm) }

/-- The comparison takes `e` of the quotient projection to the quotient projection of `e ℱ`. -/
public lemma map_π_comp_idealPowerQuotientIsoOfEquivalence_hom (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) (k : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (hqc : (e.functor.obj M).IsQuasicoherent) :
    e.functor.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) ≫
      (idealPowerQuotientIsoOfEquivalence A f e hz h I k M hqc).hom =
      cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k (e.functor.obj M)).ι := by
  have hπ : cokernel.π (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) ≫
      (PreservesCokernel.iso e.functor
        (idealPowerMultiple (baseIdealSheaf A I f) k M).ι).inv =
      e.functor.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) :=
    π_comp_cokernelComparison _ _
  have hπ' : e.functor.map (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) ≫
      (PreservesCokernel.iso e.functor
        (idealPowerMultiple (baseIdealSheaf A I f) k M).ι).hom =
      cokernel.π (e.functor.map (idealPowerMultiple (baseIdealSheaf A I f) k M).ι) := by
    rw [← hπ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [idealPowerQuotientIsoOfEquivalence, Iso.trans_hom, ← Category.assoc, hπ',
    cokernel.π_desc]

/-- **The comparison intertwines the exponent-lowering maps of the two adic towers.** Both
composites are determined by their effect on the quotient projection out of `e ℱ`, which is an
epimorphism, and there both are the projection at the lower exponent. -/
public lemma idealPowerQuotientIsoOfEquivalence_hom_naturality (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) {n m : ℕ} (hnm : n ≤ m) (M : X.Modules) [M.IsQuasicoherent]
    (hqc : (e.functor.obj M).IsQuasicoherent) :
    e.functor.map (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm M) ≫
        (idealPowerQuotientIsoOfEquivalence A f e hz h I n M hqc).hom =
      (idealPowerQuotientIsoOfEquivalence A f e hz h I m M hqc).hom ≫
        idealPowerQuotientDrop (baseIdealSheaf A I f) hnm (e.functor.obj M) := by
  refine (cancel_epi (e.functor.map (cokernel.π (C := X.Modules)
    (idealPowerMultiple (baseIdealSheaf A I f) m M).ι))).1 ?_
  rw [← Category.assoc, ← Functor.map_comp, idealPowerQuotientDrop_π,
    map_π_comp_idealPowerQuotientIsoOfEquivalence_hom, ← Category.assoc,
    map_π_comp_idealPowerQuotientIsoOfEquivalence_hom, idealPowerQuotientDrop_π]

/-- **The comparison of the transition kernels of the two adic towers**,
`e (Ker(ℱ/𝓘 ᵐ ℱ ⟶ ℱ/𝓘 ⁿ ℱ)) ≅ Ker((e ℱ)/𝓘 ᵐ (e ℱ) ⟶ (e ℱ)/𝓘 ⁿ (e ℱ))`.

`e` preserves kernels, and the two exponent-lowering maps correspond under the comparison of the
quotients, so their kernels correspond. -/
public def transitionKernelIsoOfEquivalence (e : X.Modules ≌ X.Modules)
    (hz : ∀ {P Q : X.Modules},
      e.functor.map (0 : P ⟶ Q) = (0 : e.functor.obj P ⟶ e.functor.obj Q))
    (h : ∀ (a : A) (N : X.Modules),
      e.functor.map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app N : N ⟶ N) =
        ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app (e.functor.obj N) :
          e.functor.obj N ⟶ e.functor.obj N))
    (I : Ideal A) {n m : ℕ} (hnm : n ≤ m) (M : X.Modules) [M.IsQuasicoherent]
    (hqc : (e.functor.obj M).IsQuasicoherent) :
    e.functor.obj (kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm M)) ≅
      kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm (e.functor.obj M)) :=
  PreservesKernel.iso e.functor (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm M) ≪≫
    kernel.mapIso _ _ (idealPowerQuotientIsoOfEquivalence A f e hz h I m M hqc)
      (idealPowerQuotientIsoOfEquivalence A f e hz h I n M hqc)
      (idealPowerQuotientIsoOfEquivalence_hom_naturality A f e hz h I hnm M hqc)

end Equivalence

/-! ### The twist -/

section Twist

variable (L : X.Modules) [IsInvertibleModule X L] (d : ℤ)

/-- The twist `ℱ ↦ ℱ ⊗ ℒ ^⊗ d` by an invertible module `ℒ` is an equivalence of categories. -/
public instance isEquivalence_twistFunctor : (twistFunctor L d).IsEquivalence :=
  Stacks.AmpleCohomologicalCriterion.isEquivalence_tensorRight X (tensorPowModule X L d)

/-- **Twisting carries multiplication by a base scalar to multiplication by the same scalar.**
This is `Stacks.sheafTensorRight_map_globalSmul` at the scheme spelling. -/
public lemma twistFunctor_map_baseScalar (a : A) (M : X.Modules) :
    (twistFunctor L d).map ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app M : M ⟶ M) =
      ((AlgebraicGeometry.baseScalar A (Over.mk f) a).app ((twistFunctor L d).obj M) :
        (twistFunctor L d).obj M ⟶ (twistFunctor L d).obj M) :=
  Stacks.sheafTensorRight_map_globalSmul (tensorPowModule X L d)
    ⟨fun U => AlgebraicGeometry.baseRingToSections A (Over.mk f) U a,
      fun i => Stacks.Algebraization.baseRingToSections_restrict A f i a⟩ M

/-- The twist of a quasi-coherent module is quasi-coherent.

`AlgebraicGeometry.tensorSheaf_isQuasicoherent` is keyed on the ringed-space tensor product, so
the value of the twist is first rewritten to that spelling by
`Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor_obj`. Leaving the two tensor
factors to unification against `(twistFunctor L d).obj M` instead makes the elaborator unfold
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj _` with metavariables in both factors,
which exhausts the heartbeat budget at `whnf`. -/
public lemma isQuasicoherent_twistFunctor_obj (M : X.Modules) [M.IsQuasicoherent] :
    ((twistFunctor L d).obj M).IsQuasicoherent := by
  rw [Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor_obj]
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace M
    (tensorPowModule X L d) ‹_›
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d)

/-- **The transition kernels of the `𝓘`-adic tower of a twist are the twists of those of the
module.**

`Ker(ℱ(d)/𝓘 ᵐ ℱ(d) ⟶ ℱ(d)/𝓘 ⁿ ℱ(d)) ≅ Ker(ℱ/𝓘 ᵐ ℱ ⟶ ℱ/𝓘 ⁿ ℱ) ⊗ ℒ ^⊗ d`, for `ℱ` quasi-coherent
and `ℒ` invertible. This is `transitionKernelIsoOfEquivalence` at the autoequivalence
`− ⊗ ℒ ^⊗ d`, whose compatibility with the base scalars is `twistFunctor_map_baseScalar`. -/
public def twistTransitionKernelIso (I : Ideal A) {n m : ℕ} (hnm : n ≤ m) (M : X.Modules)
    [M.IsQuasicoherent] :
    (twistFunctor L d).obj (kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm M)) ≅
      kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) hnm
        ((twistFunctor L d).obj M)) := by
  letI : (twistFunctor L d).PreservesZeroMorphisms :=
    Stacks.AmpleCohomologicalCriterion.preservesZeroMorphisms_tensorRight X
      (tensorPowModule X L d)
  have hz0 : ∀ {P Q : X.Modules},
      (twistFunctor L d).map (0 : P ⟶ Q) =
        (0 : (twistFunctor L d).obj P ⟶ (twistFunctor L d).obj Q) :=
    fun {_ _} => Functor.map_zero _ _ _
  exact transitionKernelIsoOfEquivalence A f (twistFunctor L d).asEquivalence
    (fun {_ _} => hz0) (twistFunctor_map_baseScalar A f L d) I hnm M
    (isQuasicoherent_twistFunctor_obj L d M)

end Twist

end Stacks.Cohomology.FormalFunctions

end
