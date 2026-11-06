module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of global functions over an affine object of the site

Let `Z` be an affine object of the big fppf site over `S`, let `g : Z' ⟶ Z` be a flat morphism
from an affine object, let `W` be a quasi-compact separated algebraic space with a morphism
`p : W ⟶ Z`, and let `W' = W ×_Z Z'`.  This file proves that

`Γ(Z', 𝒪) ⊗_{Γ(Z, 𝒪)} Γ(W, 𝒪_W) ⟶ Γ(W', 𝒪_{W'})`, `t ⊗ s ↦ t · s`,

the map induced by pullback of functions along the two projections of `W'`, is bijective.  This
is the degree-zero case of part (2) of Stacks 073K for the structure sheaf, with the base an
arbitrary affine object of the site instead of `Spec A` with fibre products over the terminal
object, and with the comparison map named.

The proof is the one of `StacksFrontier/AlgebraicGeometry/Spaces/GlobalFunctionsFlatBaseChange.lean`,
over a base object `Z` in place of the terminal object:

* the base change of a chart `a : U ⟶ W`, with structure morphism `s : U ⟶ Z`, is the fibre
  product `U ×_Z Z'` formed in the site, and it is a chart of `W'`; the base change of a kernel
  pair of `a` is a kernel pair of the base-changed chart;
* global functions are functions on an affine surjective étale chart `U` agreeing on its affine
  kernel pair `V` (Stacks 0792), and on the affine objects `U ×_Z Z'`, `V ×_Z Z'` the functions
  are `Γ(Z') ⊗_{Γ(Z)}` those of `U`, `V` (Γ of a cartesian square of affine schemes is
  cocartesian);
* flatness makes `Γ(Z') ⊗_{Γ(Z)} -` commute with the equalizer of the two restriction maps
  (`AlgHom.tensorEqualizerEquiv`); the algebra of that step is
  `AlgebraicGeometry.Space.bijective_of_tensor_equalizer`.

## Main results

* `AlgebraicGeometry.Space.bijective_of_tensor_equalizer`: the algebraic step.
* `AlgebraicGeometry.Space.isPullback_overObjectBaseChangeChartMap` and
  `AlgebraicGeometry.Space.isPullback_kernelPair_overObjectBaseChangeChartMap`: base change of
  charts and of kernel pairs along an object of the site.
* `AlgebraicGeometry.Space.bijective_globalFunctions_baseChange_of_flat`: **the flat base
  change of global functions over an affine object of the site.**

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### The algebraic step -/

/-- **Flat base change of an equalizer presentation.**  Let `G ⟶ C ⇉ D` and `G' ⟶ C' ⇉ D'` be
equalizer presentations (the first of `A`-algebras), let `T` be a flat `A`-algebra, and let
`T ⊗_A C ≅ C'` and `T ⊗_A D ↪ D'` intertwine the two pairs of maps.  Then a ring map
`Φ : T ⊗_A G ⟶ G'` lying over `T ⊗_A C ≅ C'` is bijective. -/
theorem bijective_of_tensor_equalizer {A T G C D G' C' D' : Type*} [CommRing A] [CommRing T]
    [CommRing G] [CommRing C] [CommRing D] [CommRing G'] [CommRing C'] [CommRing D']
    [Algebra A T] [Module.Flat A T] [Algebra A G] [Algebra A C] [Algebra A D]
    (e : G →ₐ[A] C) (he : Function.Injective e) (ρ σ : C →ₐ[A] D)
    (hrange : ∀ c, ρ c = σ c → c ∈ Set.range e)
    (e' : G' →+* C') (he' : Function.Injective e') (ρ' σ' : C' →+* D')
    (hcomp' : ∀ y, ρ' (e' y) = σ' (e' y))
    (iC : T ⊗[A] C →+* C') (hiC : Function.Bijective iC) (iD : T ⊗[A] D →+* D')
    (hiD : Function.Injective iD)
    (hρ : ∀ x, ρ' (iC x) = iD (Algebra.TensorProduct.map (AlgHom.id A T) ρ x))
    (hσ : ∀ x, σ' (iC x) = iD (Algebra.TensorProduct.map (AlgHom.id A T) σ x))
    (Φ : T ⊗[A] G →+* G')
    (hΦ : ∀ x, e' (Φ x) = iC (Algebra.TensorProduct.map (AlgHom.id A T) e x)) :
    Function.Bijective Φ := by
  have hmap : Function.Injective (Algebra.TensorProduct.map (AlgHom.id A T) e) := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := T) e.toLinearMap he
    convert this using 1
    ext x
    induction x with
    | tmul t c => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨fun x y hxy => hmap (hiC.1 ?_), fun y => ?_⟩
  · rw [← hΦ, ← hΦ, hxy]
  · obtain ⟨z, hz⟩ := hiC.2 (e' y)
    have hzeq : z ∈ AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id A T) ρ)
        (Algebra.TensorProduct.map (AlgHom.id A T) σ) := by
      show _ = _
      apply hiD
      rw [← hρ, ← hσ, hz, hcomp']
    obtain ⟨x, hx⟩ := (AlgHom.tensorEqualizerEquiv A T ρ σ).surjective ⟨z, hzeq⟩
    have hx' : Algebra.TensorProduct.map (AlgHom.id A T) (AlgHom.equalizer ρ σ).val x = z := by
      have := congrArg Subtype.val hx
      rwa [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer] at this
    have hmem : ∀ c : AlgHom.equalizer ρ σ, ∃ g, e g = c.1 := fun c => hrange c.1 c.2
    choose inv hinv using hmem
    let invA : AlgHom.equalizer ρ σ →ₐ[A] G :=
      { toFun := inv
        map_one' := he (by rw [hinv, map_one]; rfl)
        map_mul' := fun a b => he (by rw [hinv, map_mul, hinv, hinv]; rfl)
        map_zero' := he (by rw [hinv, map_zero]; rfl)
        map_add' := fun a b => he (by rw [hinv, map_add, hinv, hinv]; rfl)
        commutes' := fun r => he (by rw [hinv, AlgHom.commutes]; rfl) }
    have hcompA : e.comp invA = (AlgHom.equalizer ρ σ).val := by
      ext c; exact hinv c
    refine ⟨Algebra.TensorProduct.map (AlgHom.id A T) invA x, he' ?_⟩
    rw [hΦ, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hcompA, hx',
      hz]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of charts along an object of the site -/

section Chart

variable {Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ yoneda.obj Z) {q : X' ⟶ X} {r : X' ⟶ yoneda.obj Z'}
    (hX' : IsPullback q r f (yoneda.map g))

include hX' in
/-- The base change of a chart. For a chart `a : U ⟶ X` whose composite with `f : X ⟶ Z` is the
morphism `s : U ⟶ Z` of the site, the morphism `U ×_Z Z' ⟶ X'` it induces. -/
def overObjectBaseChangeChartMap {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (s : U ⟶ Z)
    (hs : a ≫ f = yoneda.map s) : yoneda.obj (pullback s g) ⟶ X' :=
  hX'.lift (yoneda.map (pullback.fst s g) ≫ a) (yoneda.map (pullback.snd s g)) (by
    rw [Category.assoc, hs, ← Functor.map_comp, pullback.condition, Functor.map_comp])

/-- The base-changed chart composed with `q : X' ⟶ X` is the projection `U ×_Z Z' ⟶ U` followed
by the chart. -/
@[simp] theorem overObjectBaseChangeChartMap_comp_fst {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (s : U ⟶ Z) (hs : a ≫ f = yoneda.map s) :
    overObjectBaseChangeChartMap B S hS g f hX' a s hs ≫ q =
      yoneda.map (pullback.fst s g) ≫ a :=
  hX'.lift_fst _ _ _

/-- The base-changed chart composed with `r : X' ⟶ Z'` is the projection `U ×_Z Z' ⟶ Z'`. -/
@[simp] theorem overObjectBaseChangeChartMap_comp_snd {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (s : U ⟶ Z) (hs : a ≫ f = yoneda.map s) :
    overObjectBaseChangeChartMap B S hS g f hX' a s hs ≫ r = yoneda.map (pullback.snd s g) :=
  hX'.lift_snd _ _ _

/-- **The base change of a chart is the fibre product of that chart with the projection.** -/
theorem isPullback_overObjectBaseChangeChartMap {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (s : U ⟶ Z) (hs : a ≫ f = yoneda.map s) :
    IsPullback (yoneda.map (pullback.fst s g)) (overObjectBaseChangeChartMap B S hS g f hX' a s hs)
      a q := by
  have hmap := (IsPullback.of_hasPullback s g).map yoneda
  rw [← hs, ← overObjectBaseChangeChartMap_comp_snd B S hS g f hX' a s hs] at hmap
  exact hmap.of_bot (overObjectBaseChangeChartMap_comp_fst B S hS g f hX' a s hs).symm hX'

/-- The base change of a morphism `α : V ⟶ U` of the site over `Z`. -/
def overObjectBaseChangeHom {U V : BigFppfOver B S hS} (α : V ⟶ U) (sU : U ⟶ Z) (sV : V ⟶ Z)
    (h : α ≫ sU = sV) : pullback sV g ⟶ pullback sU g :=
  pullback.lift (pullback.fst sV g ≫ α) (pullback.snd sV g)
    (by rw [Category.assoc, h, pullback.condition])

/-- The base change of `α` composed with the first projection is the first projection followed
by `α`. -/
@[simp] theorem overObjectBaseChangeHom_comp_fst {U V : BigFppfOver B S hS} (α : V ⟶ U)
    (sU : U ⟶ Z) (sV : V ⟶ Z) (h : α ≫ sU = sV) :
    overObjectBaseChangeHom B S hS g α sU sV h ≫ pullback.fst sU g = pullback.fst sV g ≫ α :=
  pullback.lift_fst _ _ _

/-- The base change of `α` commutes with the second projections to `Z'`. -/
@[simp] theorem overObjectBaseChangeHom_comp_snd {U V : BigFppfOver B S hS} (α : V ⟶ U)
    (sU : U ⟶ Z) (sV : V ⟶ Z) (h : α ≫ sU = sV) :
    overObjectBaseChangeHom B S hS g α sU sV h ≫ pullback.snd sU g = pullback.snd sV g :=
  pullback.lift_snd _ _ _

/-- The base change of a morphism of the site is cartesian over that morphism. -/
theorem isPullback_overObjectBaseChangeHom {U V : BigFppfOver B S hS} (α : V ⟶ U) (sU : U ⟶ Z)
    (sV : V ⟶ Z) (h : α ≫ sU = sV) :
    IsPullback (pullback.fst sV g) (overObjectBaseChangeHom B S hS g α sU sV h) α
      (pullback.fst sU g) := by
  have hU := IsPullback.of_hasPullback sU g
  have hV : IsPullback (pullback.fst sV g)
      (overObjectBaseChangeHom B S hS g α sU sV h ≫ pullback.snd sU g) (α ≫ sU) g := by
    rw [overObjectBaseChangeHom_comp_snd, h]
    exact IsPullback.of_hasPullback _ _
  exact hV.of_bot (by simp) hU

/-- The base change of a precomposed chart is the precomposition of the base-changed chart. -/
theorem overObjectBaseChangeChartMap_comp {U V : BigFppfOver B S hS} (α : V ⟶ U)
    (a : yoneda.obj U ⟶ X) (sU : U ⟶ Z) (sV : V ⟶ Z) (h : α ≫ sU = sV)
    (hsU : a ≫ f = yoneda.map sU) (hsV : (yoneda.map α ≫ a) ≫ f = yoneda.map sV) :
    overObjectBaseChangeChartMap B S hS g f hX' (yoneda.map α ≫ a) sV hsV =
      yoneda.map (overObjectBaseChangeHom B S hS g α sU sV h) ≫
        overObjectBaseChangeChartMap B S hS g f hX' a sU hsU := by
  refine hX'.hom_ext ?_ ?_
  · simp only [overObjectBaseChangeChartMap_comp_fst, Category.assoc]
    conv_rhs => rw [← Functor.map_comp_assoc, overObjectBaseChangeHom_comp_fst]
    simp
  · simp only [overObjectBaseChangeChartMap_comp_snd, Category.assoc]
    conv_rhs => rw [← Functor.map_comp, overObjectBaseChangeHom_comp_snd]

/-- **The base change of a kernel pair of a chart is a kernel pair of the base-changed chart.** -/
theorem isPullback_kernelPair_overObjectBaseChangeChartMap {U V : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (α β : V ⟶ U) (hkp : IsPullback (yoneda.map α) (yoneda.map β) a a)
    (sU : U ⟶ Z) (sV : V ⟶ Z) (hα : α ≫ sU = sV) (hβ : β ≫ sU = sV)
    (hsU : a ≫ f = yoneda.map sU) :
    IsPullback (yoneda.map (overObjectBaseChangeHom B S hS g α sU sV hα))
      (yoneda.map (overObjectBaseChangeHom B S hS g β sU sV hβ))
      (overObjectBaseChangeChartMap B S hS g f hX' a sU hsU)
      (overObjectBaseChangeChartMap B S hS g f hX' a sU hsU) := by
  have hsV : ∀ γ : V ⟶ U, γ ≫ sU = sV → (yoneda.map γ ≫ a) ≫ f = yoneda.map sV := by
    intro γ hγ
    rw [Category.assoc, hsU, ← Functor.map_comp, hγ]
  have hcU := isPullback_overObjectBaseChangeChartMap B S hS g f hX' a sU hsU
  have hαsq := ((isPullback_overObjectBaseChangeHom B S hS g α sU sV hα).map yoneda).flip
  have hs : IsPullback (yoneda.map (overObjectBaseChangeHom B S hS g α sU sV hα))
      (yoneda.map (pullback.fst sV g) ≫ yoneda.map β)
      (yoneda.map (pullback.fst sU g) ≫ a) a :=
    hαsq.paste_vert hkp
  rw [show yoneda.map (pullback.fst sV g) ≫ yoneda.map β =
        yoneda.map (overObjectBaseChangeHom B S hS g β sU sV hβ) ≫
          yoneda.map (pullback.fst sU g) from by
      rw [← Functor.map_comp, ← Functor.map_comp, overObjectBaseChangeHom_comp_fst],
    show yoneda.map (pullback.fst sU g) ≫ a =
      overObjectBaseChangeChartMap B S hS g f hX' a sU hsU ≫ q from
        (overObjectBaseChangeChartMap_comp_fst _ _ _ _ _ _ _ _ _).symm] at hs
  refine hs.of_bot ?_ hcU.flip
  rw [← overObjectBaseChangeChartMap_comp B S hS g f hX' α a sU sV hα hsU (hsV α hα),
    ← overObjectBaseChangeChartMap_comp B S hS g f hX' β a sU sV hβ hsU (hsV β hβ)]
  congr 1
  exact hkp.w

end Chart

/-! ### Flat base change of global functions over an affine object -/

section FlatBaseChange

variable {B S hS}

/-- Pullback of global functions along a composite `f ≫ k` is pullback along `k` followed by
pullback along `f`. -/
theorem appTop_comp_apply_toScheme {U V Z : BigFppfOver B S hS} (f : V ⟶ U) (k : U ⟶ Z)
    (x : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (f ≫ k)).appTop.hom x =
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom
        (((BigFppfOver.toScheme B S hS).map k).appTop.hom x) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- **The functions of a base change of affine objects of the site.**  For affine objects
`U`, `Z`, `Z'` and morphisms `s : U ⟶ Z`, `g : Z' ⟶ Z`, the functions on `U ×_Z Z'` are
`Γ(Z') ⊗_{Γ(Z)} Γ(U)`, the algebra structures being pullback along `g` and `s`: `Γ` carries
the cartesian square of affine schemes to a cocartesian square of rings. -/
def overObjectBaseChangeTensorRingEquiv {Z Z' U : BigFppfOver B S hS} (g : Z' ⟶ Z) (s : U ⟶ Z)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)]
    (hT : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (hU : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) =
      ((BigFppfOver.toScheme B S hS).map s).appTop.hom) :
    Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj (pullback s g), ⊤) :=
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hpo :=
    isPushout_appTop_of_isPullback
      ((IsPullback.of_hasPullback s g).map (BigFppfOver.toScheme B S hS))
  have ten := CommRingCat.isPushout_tensorProduct Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have hT' :
      CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)) =
      ((BigFppfOver.toScheme B S hS).map g).appTop := by rw [hT]; rfl
  have hU' :
      CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
      ((BigFppfOver.toScheme B S hS).map s).appTop := by rw [hU]; rfl
  (IsPushout.isoIsPushout _ _ (hT' ▸ hU' ▸ ten) hpo.flip).commRingCatIsoToRingEquiv

/-- `CommRingCat.ofHom` of the structure map of an algebra is a morphism `f` if the two agree. -/
private theorem ofHom_algebraMap_eq_of_eq {R T : CommRingCat} [Algebra R T] (f : R ⟶ T)
    (h : algebraMap R T = f.hom) : CommRingCat.ofHom (algebraMap R T) = f := by
  rw [h]; rfl

/-- The isomorphism `overObjectBaseChangeTensorRingEquiv` sends `t ⊗ₜ c` to the product of the
pullbacks of `t` and `c` along the two projections of `U ×_Z Z'`. -/
theorem overObjectBaseChangeTensorRingEquiv_tmul {Z Z' U : BigFppfOver B S hS} (g : Z' ⟶ Z)
    (s : U ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)]
    (hT : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (hU : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) =
      ((BigFppfOver.toScheme B S hS).map s).appTop.hom)
    (t : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤))
    (c : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    overObjectBaseChangeTensorRingEquiv g s hT hU (t ⊗ₜ c) =
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s g)).appTop.hom t *
        ((BigFppfOver.toScheme B S hS).map (pullback.fst s g)).appTop.hom c := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hpo :=
    isPushout_appTop_of_isPullback
      ((IsPullback.of_hasPullback s g).map (BigFppfOver.toScheme B S hS))
  have ten := CommRingCat.isPushout_tensorProduct Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have hT' := ofHom_algebraMap_eq_of_eq _ hT
  have hU' := ofHom_algebraMap_eq_of_eq _ hU
  have h1 := congrArg (fun φ => CommRingCat.Hom.hom φ t)
    (IsPushout.inl_isoIsPushout_hom _ _ (hT' ▸ hU' ▸ ten) hpo.flip)
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ c)
    (IsPushout.inr_isoIsPushout_hom _ _ (hT' ▸ hU' ▸ ten) hpo.flip)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  show (IsPushout.isoIsPushout _ _ (hT' ▸ hU' ▸ ten) hpo.flip).hom.hom (t ⊗ₜ c) = _
  rw [← h1, ← h2, ← map_mul]
  congr 1
  show _ = (t ⊗ₜ 1) * (1 ⊗ₜ _)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Under `AlgebraicGeometry.Space.overObjectBaseChangeTensorRingEquiv`, restriction along the
base change of a morphism `α : V ⟶ U` over `Z` is `Γ(Z') ⊗_{Γ(Z)}` restriction along `α`. -/
theorem overObjectBaseChangeTensorRingEquiv_naturality {Z Z' U V : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (α : V ⟶ U) (sU : U ⟶ Z) (sV : V ⟶ Z) (h : α ≫ sU = sV)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)]
    (hT : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (hU : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) =
      ((BigFppfOver.toScheme B S hS).map sU).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hV : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =
      ((BigFppfOver.toScheme B S hS).map sV).appTop.hom)
    (ρ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hρ : ∀ c, ρ c = ((BigFppfOver.toScheme B S hS).map α).appTop.hom c)
    (x : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (overObjectBaseChangeHom B S hS g α sU sV h)).appTop.hom
        (overObjectBaseChangeTensorRingEquiv g sU hT hU x) =
      overObjectBaseChangeTensorRingEquiv g sV hT hV
        (Algebra.TensorProduct.map
          (AlgHom.id Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)) ρ x) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t c =>
    rw [overObjectBaseChangeTensorRingEquiv_tmul, Algebra.TensorProduct.map_tmul,
      overObjectBaseChangeTensorRingEquiv_tmul, map_mul, hρ]
    congr 1
    · rw [← appTop_comp_apply_toScheme, overObjectBaseChangeHom_comp_snd]
      rfl
    · rw [← appTop_comp_apply_toScheme, overObjectBaseChangeHom_comp_fst,
        appTop_comp_apply_toScheme]

/-- **Flat base change of global functions over an affine object of the site, in degree
zero.**  Let `g : Z' ⟶ Z` be a flat morphism of affine objects of the big fppf site over `S`,
let `W` be a quasi-compact separated algebraic space with a morphism `p : W ⟶ Z`, and let
`W' = W ×_Z Z'` with projections `q : W' ⟶ W` and `r : W' ⟶ Z'`.  Then the ring map

`Γ(Z', 𝒪) ⊗_{Γ(Z, 𝒪)} Γ(W, 𝒪_W) ⟶ Γ(W', 𝒪_{W'})`, `t ⊗ s ↦ r^* t · q^* s`,

is bijective.  Here the `Γ(Z, 𝒪)`-algebra structures are pullback of functions along `g` and
along `p` (the latter pinned down on every étale scheme chart of `W`), `r^*` is pullback of
functions along `r` (pinned down the same way) and `q^*` is
`AlgebraicGeometry.Space.globalFunctionsMap`.

This is the degree-zero case of part (2) of Stacks 073K for the structure sheaf, under
separatedness in place of quasi-separatedness, over an affine base object of the site: an
affine surjective étale chart `U` of `W` has an affine kernel pair `V` (Stacks 03H6 and Stacks
08GB), global functions are functions on `U` agreeing on `V` (Stacks 0792), the base changes
`U ×_Z Z'` and `V ×_Z Z'` are a chart of `W'` and its kernel pair, with functions
`Γ(Z') ⊗_{Γ(Z)}` those of `U` and `V`, and flatness makes the tensor product commute with the
equalizer (`AlgebraicGeometry.Space.bijective_of_tensor_equalizer`). -/
@[sga "3 VIB 11.1" "special case"]
theorem bijective_globalFunctions_baseChange_of_flat (hZ : B.Contains (⊤_ Scheme.{u}))
    {Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    {W W' : AlgebraicSpaces B S hS} (p : W.obj ⟶ yoneda.obj Z) (q : W' ⟶ W)
    (r : W'.obj ⟶ yoneda.obj Z') (hsq : IsPullback q.hom r p (yoneda.map g))
    (hqc : IsQuasiCompactSpace B S hS W.obj) (hsep : IsAbsolutelySeparated B S hS hZ W.obj)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)]
    (hT : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj)]
    (hG : ∀ c : SmallEtale B S hS W.obj,
      (globalFunctionsChartRestriction B S hS W c).comp
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj)) =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c)).appTop.hom)
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) →+* globalFunctions B S hS W'.obj)
    (hψ : ∀ c : SmallEtale B S hS W'.obj,
      (globalFunctionsChartRestriction B S hS W' c).comp ψ =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS r c)).appTop.hom)
    (Φ : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
        globalFunctions B S hS W.obj →+* globalFunctions B S hS W'.obj)
    (hΦ : ∀ t s, Φ (t ⊗ₜ s) = ψ t * globalFunctionsMap B S hS q s) :
    Function.Bijective Φ := by
  classical
  have : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) := by
    rw [← RingHom.flat_algebraMap_iff, hT]
    exact ((BigFppfOver.toScheme B S hS).map g).flat_appTop
  -- An affine surjective étale chart of `W`, with an affine kernel pair.
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS W.obj
      W.property).mp hqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (𝟙 U)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      a := by
    have h := haet U (yoneda.map (𝟙 U)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  obtain ⟨Vq, pV, β0, hkp0⟩ := isAffineHom_of_affine_source_of_isAbsolutelySeparated
    B S hS hZ ⟨U, hUaff⟩ a hsep ⟨U, hUaff⟩ a
  obtain ⟨α, hα0⟩ : ∃ α : (BigAffineFppf.inclusion B S hS).obj Vq ⟶ U, yoneda.map α = pV :=
    ⟨yoneda.preimage pV, yoneda.map_preimage pV⟩
  let β : (BigAffineFppf.inclusion B S hS).obj Vq ⟶ U := β0
  have hkp : IsPullback (yoneda.map α) (yoneda.map β) a a := by rw [hα0]; exact hkp0
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj Vq)) := Vq.property
  -- The structure morphisms to `Z`.
  set sU : U ⟶ Z := yoneda.preimage (a ≫ p) with hsUdef
  have hsU : a ≫ p = yoneda.map sU := (yoneda.map_preimage _).symm
  set sV : (BigAffineFppf.inclusion B S hS).obj Vq ⟶ Z := α ≫ sU with hsVdef
  have hβ : β ≫ sU = sV := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, ← hsU, ← Category.assoc, ← Category.assoc, hkp.w])
  -- The charts of `W`.
  have hαet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) α :=
    haet'.property a (yoneda.map β) α hkp.flip
  let Uc : SmallEtale B S hS W.obj := ⟨CostructuredArrow.mk a, haet'⟩
  let Vc : SmallEtale B S hS W.obj :=
    ⟨CostructuredArrow.mk (yoneda.map α ≫ a), chart_preimage_etale B S hS W a haet' α hαet⟩
  let αc : Vc ⟶ Uc := ObjectProperty.homMk (CostructuredArrow.homMk α rfl)
  let βc : Vc ⟶ Uc := ObjectProperty.homMk (CostructuredArrow.homMk β hkp.w.symm)
  have hcov : (SmallEtale.topology B S hS W.obj).CoversTop (fun _ : Unit => Uc) :=
    GrothendieckTopology.coversTop_punit
      (SmallEtale.coversTop_of_isSurjective B S hS W.obj W.property Uc
        (isSurjective_of_presheafSurjective B S hS a hasurj))
  -- The charts of `W'`.
  let a' := overObjectBaseChangeChartMap B S hS g p hsq a sU hsU
  have hcP := isPullback_overObjectBaseChangeChartMap B S hS g p hsq a sU hsU
  let α' := overObjectBaseChangeHom B S hS g α sU sV rfl
  let β' := overObjectBaseChangeHom B S hS g β sU sV hβ
  have hkp' : IsPullback (yoneda.map α') (yoneda.map β') a' a' :=
    isPullback_kernelPair_overObjectBaseChangeChartMap B S hS g p hsq α β hkp sU sV rfl hβ hsU
  have haet'' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a' :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hcP haet'
  have hα'et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) α' :=
    haet''.property a' (yoneda.map β') α' hkp'.flip
  let Uc' : SmallEtale B S hS W'.obj := ⟨CostructuredArrow.mk a', haet''⟩
  let Vc' : SmallEtale B S hS W'.obj :=
    ⟨CostructuredArrow.mk (yoneda.map α' ≫ a'),
      chart_preimage_etale B S hS W' a' haet'' α' hα'et⟩
  let αc' : Vc' ⟶ Uc' := ObjectProperty.homMk (CostructuredArrow.homMk α' rfl)
  let βc' : Vc' ⟶ Uc' := ObjectProperty.homMk (CostructuredArrow.homMk β' hkp'.w.symm)
  have hcov' : (SmallEtale.topology B S hS W'.obj).CoversTop (fun _ : Unit => Uc') := by
    have hsurj' := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hcP hasurj
    exact GrothendieckTopology.coversTop_punit
      (SmallEtale.coversTop_of_isSurjective B S hS W'.obj W'.property Uc'
        (isSurjective_of_presheafSurjective B S hS _ hsurj'))
  -- The algebra structures on the functions of the charts.
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map sU).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Vq), ⊤) :=
    ((BigFppfOver.toScheme B S hS).map sV).appTop.hom.toAlgebra
  let e : globalFunctions B S hS W.obj →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    { globalFunctionsChartRestriction B S hS W Uc with
      commutes' := fun x => RingHom.congr_fun (hG Uc) x }
  let ρ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Vq), ⊤) :=
    { ((BigFppfOver.toScheme B S hS).map α).appTop.hom with
      commutes' := fun x => (appTop_comp_apply_toScheme α sU x).symm }
  let σ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Vq), ⊤) :=
    { ((BigFppfOver.toScheme B S hS).map β).appTop.hom with
      commutes' := fun x => by
        show _ = ((BigFppfOver.toScheme B S hS).map sV).appTop.hom x
        rw [← hβ, appTop_comp_apply_toScheme]
        rfl }
  have hbij := bijective_globalFunctionsToEqualizer W αc βc hcov hkp
  have hbij' := bijective_globalFunctionsToEqualizer W' αc' βc' hcov' hkp'
  -- The tensor product descriptions of the functions of the base-changed charts.
  have hρ : ∀ c, ρ c = ((BigFppfOver.toScheme B S hS).map α).appTop.hom c := fun _ => rfl
  have hσ : ∀ c, σ c = ((BigFppfOver.toScheme B S hS).map β).appTop.hom c := fun _ => rfl
  let iC := overObjectBaseChangeTensorRingEquiv g sU hT rfl
  let iD := overObjectBaseChangeTensorRingEquiv g sV hT rfl
  refine bijective_of_tensor_equalizer e ?_ ρ σ ?_
    (globalFunctionsChartRestriction B S hS W' Uc') ?_
    ((BigFppfOver.toScheme B S hS).map α').appTop.hom
    ((BigFppfOver.toScheme B S hS).map β').appTop.hom
    (fun y => chartSectionsRestriction_mem_eqLocus W' αc' βc' y)
    iC.toRingHom iC.bijective iD.toRingHom iD.injective
    (overObjectBaseChangeTensorRingEquiv_naturality g α sU sV rfl hT rfl rfl ρ hρ)
    (overObjectBaseChangeTensorRingEquiv_naturality g β sU sV hβ hT rfl rfl σ hσ) Φ ?_
  · intro s t hst
    exact hbij.1 (Subtype.ext hst)
  · intro c hc
    obtain ⟨s, hs⟩ := hbij.2 ⟨c, hc⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  · intro s t hst
    exact hbij'.1 (Subtype.ext hst)
  · intro x
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t s =>
      rw [hΦ, map_mul, Algebra.TensorProduct.map_tmul]
      show _ = overObjectBaseChangeTensorRingEquiv g sU hT rfl (t ⊗ₜ e s)
      rw [overObjectBaseChangeTensorRingEquiv_tmul]
      congr 1
      · have hm : smallEtaleChartMapToBase B S hS r Uc' = pullback.snd sU g :=
          yoneda.map_injective (by
            rw [yoneda_map_smallEtaleChartMapToBase]
            exact overObjectBaseChangeChartMap_comp_snd B S hS g p hsq a sU hsU)
        rw [← RingHom.comp_apply, hψ Uc', hm]
      · exact globalFunctionsChartRestriction_globalFunctionsMap B S hS q Uc' Uc
          (pullback.fst sU g) (overObjectBaseChangeChartMap_comp_fst B S hS g p hsq a sU hsU).symm s

end FlatBaseChange

end AlgebraicGeometry.Space

end
