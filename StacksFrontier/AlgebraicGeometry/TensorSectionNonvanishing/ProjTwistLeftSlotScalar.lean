module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistScalarTriviality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor

/-!
# Multiplication by a homogeneous scalar of positive degree, in the **left** tensor slot

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `f ∈ 𝒮 d` be homogeneous and let `ℱ`
be a sheaf of `𝒪_X`-modules. `TensorSectionNonvanishing/ProjTwistScalarTriviality.lean` proves
that multiplication by `f ^ m` is bijective on `Γ(W, ℱ(n d))` for every open `W ⊆ D₊(f)` and
every **integer** `n`. That statement is about `ℱ ⊗ 𝒪(nd)`: the morphism is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap`, which is `𝟙_ℱ` tensored with
the morphism of twisting sheaves, so the twist sits in the **right** slot — as it does in every
twisting result of that directory.

This file carries it to the **left** slot, `𝒪(nd) ⊗ ℱ`, and identifies the left-slot tensor map
with the action of the geometric factor `N ↦ F ⊗ (f')^* Ñ` on its **fixed** factor. Those two
steps together are what lets the local invertibility be read inside
`Stacks.Blowup.twistScalarFactorMap`, where the twist is the left factor.

## Why the braiding is needed here and was not needed for a base scalar

For a scalar of the base ring the transport is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorMap_smul_id_app_eq_smul_id`, and it
needs no braiding: `r • 𝟙 F` is an endomorphism of `F`, so `φ ⊗ 𝟙` and `𝟙 ⊗ φ` are
endomorphisms of *the same* object and agree already on pure tensors of local sections.

A homogeneous scalar of degree `i > 0` is a morphism `𝒪(n) ⟶ 𝒪(n + i)` of **different** twisting
sheaves, so `φ ⊗ 𝟙 : 𝒪(n) ⊗ ℱ ⟶ 𝒪(n+i) ⊗ ℱ` and `𝟙 ⊗ φ : ℱ ⊗ 𝒪(n) ⟶ ℱ ⊗ 𝒪(n+i)` have
different sources and different targets, and nothing but a braiding relates them. The braiding is
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap`, whose naturality
`tensorSheafSwap_naturality` is already stated in the `tensorSheafMap` vocabulary the twisting
results use — `swap ≫ (g ⊗ f) = (f ⊗ g) ≫ swap` — so at `g = 𝟙` it is exactly the exchange
wanted, and no further comparison of tensor products is involved.

## Implementation notes

**The three spellings of one tensor product cost nothing here.**
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`,
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` are the same object, and the
corresponding morphisms the same morphism, by `rfl`:
`Stacks.TensorSheafDedup.tensorSheaf_eq` and `…tensorSheafMap_eq_sheafifyMap`. So the statements
below are written at the `TensorStalkRingedSpace` spelling, which is the one both the braiding
and `twistSheafScalarMap` are stated at, and the definitional equalities are crossed by `exact`
inside the proofs. The only comparison that is not `rfl` is the one of
`tensorFactorMap_app_eq_tensorSheafMap`, between `f ⊗ₘ 𝟙 M` and `f ▷ M` at the level of
presheaves of modules, and it is `MonoidalCategory.tensorHom_id` sheafified by `congrArg` — the
device of `TopDegreeBaseChange/GeometricFactorBaseScalar.lean`.

**The bijectivity is transported as a statement about functions, not about morphisms.** The
known invertibility is `Function.Bijective` of a map on sections, so the conjugation by the
braiding is `bijective_of_comp_eq_comp`, a statement about four bare functions; the only
categorical input is that an isomorphism of sheaves of modules is bijective on sections, which
is `CategoryTheory.ConcreteCategory.bijective_of_isIso` at
`CategoryTheory.SheafOfModules.evaluation`. Nothing is rewritten under a morphism.

**The twist degrees are variables.** The existing statements carry the degrees as the products
`m * d`, `n * d` and `j * d`; a consumer at `d = 1` has degrees `c`, `q'` and `q`, which are not
definitionally those products, and reconciling them under a morphism would need a transport
along an equality of degrees. `bijective_twistSheafScalarMap_pow_app_of_eq` therefore carries
them as variables constrained by propositional equations and recovers their form by `subst`.

## Main results

* `ProjTwistLeftSlot.bijective_tensorSheafMap_id_right_app`: **the slot exchange.** `φ ⊗ 𝟙` is
  bijective on the sections over an object as soon as `𝟙 ⊗ φ` is.
* `ProjTwistLeftSlot.bijective_tensorSheafMap_twistScalarSheafMap_pow_app`: **multiplication by
  `f ^ m` is bijective on `Γ(W, 𝒪(N) ⊗ ℱ)` for every `W ⊆ D₊(f)`**, at every integer twist.
* `ProjTwistLeftSlot.tensorFactorMap_app_eq_tensorSheafMap`: the action of `F ⊗ -` on a morphism
  of its fixed factor is that morphism tensored with the identity.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u v₁ u₁

namespace Stacks.AlgebraicGeometry.ProjTwistLeftSlot

/-! ### A bijection transported across a commuting square of bijections -/

/-- **A map conjugate to a bijection by two bijections is a bijection.** -/
theorem bijective_of_comp_eq_comp {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    {a : α → γ} {b : β → δ} (ha : Function.Bijective a) (hb : Function.Bijective b)
    (hg : Function.Bijective g) (h : ∀ x, b (f x) = g (a x)) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    exact ha.1 (hg.1 (((h x).symm.trans (congrArg b hxy)).trans (h y)))
  · intro z
    obtain ⟨y, hy⟩ := hg.2 (b z)
    obtain ⟨x, rfl⟩ := ha.2 y
    exact ⟨x, hb.1 ((h x).trans hy)⟩

/-! ### An isomorphism of sheaves of modules is bijective on sections -/

/-- **An isomorphism of sheaves of modules is bijective on the sections over every object.** -/
theorem bijective_iso_hom_val_app {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Bijective (e.hom.val.app U) := by
  have : IsIso ((_root_.SheafOfModules.evaluation R U).map e.hom) := inferInstance
  exact ConcreteCategory.bijective_of_isIso ((_root_.SheafOfModules.evaluation R U).map e.hom)

/-- A bijectivity on the sections over an object may be read along an equality of morphisms.
Stated so that an identification of morphisms is crossed by `subst` rather than rewritten under
`Function.Bijective`, whose motive mentions the morphism's type. -/
theorem bijective_val_app_congr {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} {φ ψ : M ⟶ N} (h : φ = ψ)
    (U : Cᵒᵖ) (hb : Function.Bijective (ψ.val.app U)) :
    Function.Bijective (φ.val.app U) := by
  subst h
  exact hb

/-! ### The left slot, from the right slot, by the braiding -/

/-- **Tensoring a morphism with the identity of a fixed second factor is bijective on the
sections over an object as soon as tensoring the identity with it in the other slot is.** -/
theorem bijective_tensorSheafMap_id_right_app (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    {L L' F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (φ : L ⟶ L') (U : (Opens X.carrier)ᵒᵖ)
    (h : Function.Bijective
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        ((𝟙 F, φ) : ((F, L) : _ × _) ⟶ (F, L'))).val.app U)) :
    Function.Bijective
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        ((φ, 𝟙 F) : ((L, F) : _ × _) ⟶ (L', F))).val.app U) := by
  refine bijective_of_comp_eq_comp
    (bijective_iso_hom_val_app
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X L F) U)
    (bijective_iso_hom_val_app
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X L' F) U)
    h fun x => ?_
  exact congrArg
    (fun z : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj F ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj F).obj L' => z.val.app U x)
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_naturality X φ (𝟙 F)).symm

/-! ### Multiplication by `f ^ m` in the left slot, on `Proj` -/

section Proj

open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (pow_mem_degree
  bijective_twistSheafScalarMap_pow_app)

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] {f : S} {d : ℕ}

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **Multiplication by `f ^ m` is bijective on the sections of `ℱ(N)` over every open inside
`D₊(f)`**, with the twist degrees and the degree of the scalar carried as variables.

This is `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_twistSheafScalarMap_pow_app`
generalised by `subst`: the degrees there are the products `m * d`, `n * d` and `j * d`, which a
consumer whose degrees are already simplified cannot match without transporting along an
equality of degrees. Here the three are variables constrained by propositional equations, so no
transport ever occurs; the membership proof of the scalar is likewise a variable, which costs
nothing since it is a `Prop`. -/
theorem bijective_twistSheafScalarMap_pow_app_of_eq (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    {i : ℕ} {N J : ℤ} (hi : i = m * d) (hN : N = n * d) (hJ : J = j * d)
    (ha : f ^ m ∈ 𝒮 i) (hj : n + (m : ℤ) = j) (hdeg : (i : ℤ) + N = J)
    (F : _root_.SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective
      ((twistSheafScalarMap 𝒮 F i N J hdeg ⟨f ^ m, ha⟩).val.app (op W)) := by
  subst hi
  subst hN
  subst hJ
  exact bijective_twistSheafScalarMap_pow_app 𝒮 hf m n j hj hdeg F hW

/-- **Multiplication by `f ^ m` is bijective on the sections of `𝒪(N) ⊗ ℱ` over every open inside
`D₊(f)`** — the same statement with the twisting sheaf in the **left** tensor slot.

The statements of `TensorSectionNonvanishing/` are all about `ℱ ⊗ 𝒪(N)`, while the
geometric factor `N ↦ 𝒪_X(q) ⊗ p^*Ñ` of the blowup carries the twist on the left; the two
morphisms `φ ⊗ 𝟙` and `𝟙 ⊗ φ` are endomorphisms of the same object only when `φ` is, which for
a scalar of positive degree it is not. So the braiding
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap` is what relates them, through
`bijective_tensorSheafMap_id_right_app`. -/
theorem bijective_tensorSheafMap_twistScalarSheafMap_pow_app (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    {i : ℕ} {N J : ℤ} (hi : i = m * d) (hN : N = n * d) (hJ : J = j * d)
    (ha : f ^ m ∈ 𝒮 i) (hj : n + (m : ℤ) = j) (hdeg : (i : ℤ) + N = J)
    (F : _root_.SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.sheaf)).map
        ((twistScalarSheafMap 𝒮 i N J hdeg ⟨f ^ m, ha⟩, 𝟙 F) :
          ((_, _) : _ × _) ⟶ (_, _))).val.app (op W)) :=
  bijective_tensorSheafMap_id_right_app _ _ _
    (bijective_twistSheafScalarMap_pow_app_of_eq 𝒮 hf m n j hi hN hJ ha hj hdeg F hW)

end Proj

/-! ### The geometric factor's action on the fixed factor is a left-slot tensor map -/

section GeometricFactor

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (tensorFactor tensorFactorMap tildeFactor
  pullbackFactor geometricFactorFormula geometricFactorFormulaMap)

variable (R : Type u) [CommRing R] (V : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))

/-- **A morphism of the fixed factor of `F ⊗ -` acts as that morphism tensored with the identity
of the variable factor.** -/
theorem tensorFactorMap_app_eq_tensorSheafMap {F F' : V.left.Modules} (f : F ⟶ F')
    (M : V.left.Modules) :
    (tensorFactorMap R V f).app M =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor V.left.toRingedSpace.sheaf)).map
        ((f, 𝟙 M) : ((F, M) : _ × _) ⟶ (F', M)) := by
  let : MonoidalCategory (PresheafOfModules.{u} V.left.ringCatSheaf.obj) :=
    Stacks.SheafOfModules.monoidalCategoryPresheafOfModules V.left.presheaf
      (_root_.AlgebraicGeometry.ringSheafCond V.left)
  refine Eq.trans (congrArg
    (Stacks.SheafOfModules.TensorSheafification.sheafify V.left.presheaf
      (_root_.AlgebraicGeometry.ringSheafCond V.left)).map
    (MonoidalCategory.tensorHom_id f.val M.val).symm) ?_
  exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ f (𝟙 M)).symm

/-- **A morphism of the fixed factor of the geometric factor `N ↦ F ⊗ (f')^* Ñ` is bijective on
the sections over an object as soon as the left-slot tensor map is**, at every `R`-module `N`.

Only the tensor step of the geometric factor depends on the fixed factor, so this is
`tensorFactorMap_app_eq_tensorSheafMap` read at the pullback of `Ñ`. The hypothesis is stated for
every sheaf of modules rather than for that one object, which is what lets a consumer supply a
statement proved for an arbitrary `ℱ` without naming the pullback. -/
theorem bijective_geometricFactorFormulaMap_app {F F' : V.left.Modules} (f : F ⟶ F')
    (N : ModuleCat.{u} R) (U : (Opens V.left.carrier)ᵒᵖ)
    (h : ∀ M : V.left.Modules, Function.Bijective
      (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor V.left.toRingedSpace.sheaf)).map
        ((f, 𝟙 M) : ((F, M) : _ × _) ⟶ (F', M))).val.app U)) :
    Function.Bijective (((geometricFactorFormulaMap R V f).app N).val.app U) :=
  bijective_val_app_congr
    (tensorFactorMap_app_eq_tensorSheafMap R V f
      ((pullbackFactor R V).obj ((tildeFactor R).obj N))) U
    (h ((pullbackFactor R V).obj ((tildeFactor R).obj N)))

end GeometricFactor

end Stacks.AlgebraicGeometry.ProjTwistLeftSlot

end
