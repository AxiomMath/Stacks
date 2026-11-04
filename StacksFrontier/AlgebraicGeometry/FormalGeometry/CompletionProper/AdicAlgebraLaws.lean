module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicTensorSystemDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.TensorComparisonCoherence

/-!
# Commutativity of the multiplication descended to the algebraization

`AlgebraicGeometry.existsUnique_multiplication_of_adicAlgebraModuleSystem` descends the
multiplications of a cartesian system `(B n)` of quasi-coherent algebra sheaves to a single
morphism `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` on the algebraization, and
`AlgebraicGeometry.mulPresheafOfHom` turns `μ` into the `mul` field of a
`Stacks.FundamentalGroup.ModuleAlgebraData`. That structure asks for three laws on local
sections. **This file proves the first of them, `mul_comm`.**

## Main results

* `AlgebraicGeometry.tensorSheafSwap_comp_multiplication` — **the multiplication of an algebra
  sheaf is commutative, as a morphism of sheaves of modules**: precomposing it with the symmetry
  constraint of [Stacks, Tag 01CA] changes nothing. Checked on local pure tensors, where it is
  `mul_comm` in the commutative ring of sections.
* `AlgebraicGeometry.mulPresheafOfHom_comm` — **the `mul_comm` clause of
  `Stacks.FundamentalGroup.ModuleAlgebraData` for `AlgebraicGeometry.mulPresheafOfHom`**, from
  the sheaf-level identity `swap ≫ μ = μ`. This is
  `AlgebraicGeometry.mulPresheafOfHom_app` together with the action of the symmetry on a local
  pure tensor, and nothing else; it is stated over a variable scheme and a variable `μ`.
* `AlgebraicGeometry.tensorSheafSwap_comp_tensorDescentApp` — **the component of the
  multiplication on an adic thickening absorbs the symmetry.** This is where the Tag 01CD
  coherence enters: `AlgebraicGeometry.tensorDescentApp` has the comparison as its first factor,
  `AlgebraicGeometry.schemePullbackTensorIso_tensorSheafSwap` moves the symmetry past it,
  `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_naturality` moves it past the two
  tensor factors, and the commutativity of the algebra sheaf absorbs it. Stated over variable
  schemes, so that the instantiation at the fibre products elaborates.
* `AlgebraicGeometry.tensorSheafSwap_comp_hom_of_adicAlgebraMulApp` — **`swap ≫ μ = μ` for the
  descended multiplication**, by the uniqueness clause of
  `AlgebraicGeometry.existsUnique_multiplication_of_adicAlgebraModuleSystem`: both `μ` and
  `swap ≫ μ` restrict to `AlgebraicGeometry.adicAlgebraMulApp` on every thickening, and there is
  only one morphism that does.
* `AlgebraicGeometry.mulPresheafOfHom_comm_of_adicAlgebraMulApp` — the previous two composed:
  **the `mul_comm` clause for the multiplication a cartesian system of algebra sheaves descends
  to.**

## What is still owed for `hdata`

`mul_assoc` and `one_mul`. Both coherences they need are proved at the strict-monoidal spelling —
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator` and
`pullbackTensorComparison_leftUnitor` — but neither is crossed to this development's spelling
here, the way
`AlgebraicGeometry.schemePullbackTensorIso_tensorSheafSwap` crosses the braided one. For
`mul_assoc` the crossing is not the whole cost: the identity is between two morphisms out of
`AlgebraicGeometry.tensorCubeProperOver`, and besides the associator it needs the comparison's
compatibility with the two whiskerings
(`Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_left` and `..._right`) and a
triple-tensor analogue of `AlgebraicGeometry.tensorDescentApp`. For `one_mul` the `unit` field of
the `ModuleAlgebraData` is not built at all: `AdicTensorSystemDescent.lean` descends the
multiplication only.

## Spelling

Nothing here mentions `Stacks.RingedSpace.structureSheafRing`,
`CategoryTheory.Sheaf.toRingCat` or `Stacks.RingedSpace.structureRingSheaf`, and no equation
between two spellings of the sheaf of rings is proved. The two local instances that the crossing
needs are the existing ones, turned on by `attribute [local instance]`: the two monoidal/braided
structures of `Stacks.PullbackTensorCoherence`, and
`AlgebraicGeometry.moduleOnSectionsAtSchemePresheaf` of `AdicTensorSystemDescent.lean` — so no
third copy of that instance is declared.

Every statement over the fibre products goes through `AlgebraicGeometry.tensorDescentApp` and
`AlgebraicGeometry.adicAlgebraMulApp`, both definitions, so no
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap` is elaborated over one; and the
category algebra of `AlgebraicGeometry.tensorSheafSwap_comp_tensorDescentApp` is split off into
`swapDescentChain` in an abstract category, for the reason recorded at
`AlgebraicGeometry.descentChain` in `AdicTensorSystemComparison.lean` —
`CategoryTheory.Category.assoc` cannot be matched by `rw` at
`AlgebraicGeometry.Scheme.Modules`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication multiplication_tmul mulSection)
open Stacks.AffineAlgebraEquivalence (algebraPullback)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.SheafOfModules.TensorPresentations (tensorSheafSwap tensorSheafSwap_naturality
  tensorSheafSwap_app_toTensorSheafSection)

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory
  moduleOnSectionsAtSchemePresheaf

/-! ### The multiplication of an algebra sheaf is commutative -/

/-- A morphism precomposed with the symmetry, on a local pure tensor, is the morphism on the
swapped pure tensor. -/
private theorem swap_comp_app_toTensorSheafSection {Y : Scheme.{u}} (E : Y.Modules) {F : Y.Modules}
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ F)
    (U : Y.Opens) (x y : E.val.obj (.op U)) :
    (((tensorSheafSwap Y.toRingedSpace E E).hom ≫ μ).val.app (.op U)).hom
        (toTensorSheafSection Y.toRingedSpace E E (.op U) (x ⊗ₜ[Γ(Y, U)] y)) =
      (μ.val.app (.op U)).hom
        (toTensorSheafSection Y.toRingedSpace E E (.op U) (y ⊗ₜ[Γ(Y, U)] x)) :=
  (Stacks.SheafOfModules.comp_val_app_apply _ _ _ _).trans
    (congrArg (fun z => (μ.val.app (.op U)).hom z)
      (tensorSheafSwap_app_toTensorSheafSection Y.toRingedSpace E E U x y))

/-- **The multiplication of an algebra sheaf is commutative, as a morphism of sheaves of
modules.** Precomposing `Stacks.RelativeSpec.AlgebraSheaf.multiplication` with the symmetry
constraint of [Stacks, Tag 01CA] changes nothing.

Both sides are morphisms out of the tensor square of the underlying module, so
`Stacks.PullbackTensorCoherence.tensor_hom_ext` compares them on local pure tensors; there the
symmetry exchanges the two factors
(`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection`), the
multiplication is the product of sections
(`Stacks.RelativeSpec.AlgebraSheaf.multiplication_tmul`), and what remains is `mul_comm` in the
commutative ring `A(U)`. -/
public theorem tensorSheafSwap_comp_multiplication {W : Scheme.{u}} (A : AlgebraSheaf W) :
    (tensorSheafSwap W.toRingedSpace (AlgebraSheaf.underlyingModule A)
          (AlgebraSheaf.underlyingModule A)).hom ≫ multiplication A =
      multiplication A := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b => ?_
  have hcomm : ∀ x y : A.right.obj.obj U, mulSection A U x y = mulSection A U y x :=
    fun x y => mul_comm x y
  exact (swap_comp_app_toTensorSheafSection _ _ U.unop a b).trans
    (((multiplication_tmul A U b a).trans (hcomm b a)).trans (multiplication_tmul A U a b).symm)

/-- **The `mul_comm` clause of `Stacks.FundamentalGroup.ModuleAlgebraData` for the
presheaf-level multiplication built from a morphism out of the sheafified tensor square.** Given
the sheaf-level identity `swap ≫ μ = μ`, the induced `mul` is commutative on local sections.

By `AlgebraicGeometry.mulPresheafOfHom_app` each side is `μ` evaluated at the
sheafification-unit image of a pure tensor, and the symmetry exchanges the two factors there, so
the hypothesis applies directly. Nothing about `μ` is used beyond the hypothesis: it is stated
over a variable scheme and a variable morphism, and the descent supplies the hypothesis
separately. -/
public theorem mulPresheafOfHom_comm {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (hμ : (tensorSheafSwap Y.toRingedSpace E E).hom ≫ μ = μ)
    (U : (Y.Opens)ᵒᵖ) (x y : E.val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U (x ⊗ₜ[Γ(Y, U.unop)] y) =
      PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U (y ⊗ₜ[Γ(Y, U.unop)] x) :=
  (mulPresheafOfHom_app E μ U (x ⊗ₜ y)).trans
    ((congrArg (fun k : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E =>
        (k.val.app U).hom (toTensorSheafSection Y.toRingedSpace E E U (x ⊗ₜ y))) hμ).symm.trans
      ((swap_comp_app_toTensorSheafSection E μ U.unop x y).trans
        (mulPresheafOfHom_app E μ U (y ⊗ₜ x)).symm))

/-! ### The component absorbs the symmetry -/

/-- The three steps of `AlgebraicGeometry.tensorSheafSwap_comp_tensorDescentApp`, in an abstract
category. Stated here and not in place for the reason recorded at
`AlgebraicGeometry.descentChain`: `CategoryTheory.Category.assoc` cannot be matched by `rw` at
`AlgebraicGeometry.Scheme.Modules`, whose category instance is reached through a `def`. -/
private theorem swapDescentChain {C : Type*} [Category C] {T Q R O P' : C}
    {s : T ⟶ T} {c : T ⟶ Q} {sq : Q ⟶ Q} {t : Q ⟶ R} {sm : R ⟶ R} {m : R ⟶ O} {d : O ⟶ P'}
    (h₁ : s ≫ c = c ≫ sq) (h₂ : sq ≫ t = t ≫ sm) (h₃ : sm ≫ m = m) :
    s ≫ c ≫ t ≫ m ≫ d = c ≫ t ≫ m ≫ d := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]

/-- **The component of the multiplication on a thickening absorbs the symmetry.** For
`w : W ⟶ W''`, a module `N` on `W''` and a multiplication `mul` on `M` that is commutative in the
sense of `AlgebraicGeometry.tensorSheafSwap_comp_multiplication`, precomposing
`AlgebraicGeometry.tensorDescentApp` with the inverse image of the symmetry of `N ⊗ N` changes
nothing.

Three inputs, and no others: the symmetry passes the comparison of [Stacks, Tag 01CD]
(`AlgebraicGeometry.schemePullbackTensorIso_tensorSheafSwap`), it passes the two tensor factors
(`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_naturality` at `ε`, `ε`), and `mul`
absorbs it. Every scheme is a variable, so that the instantiation at the fibre product
`AlgebraicGeometry.adicBaseChange A I f n` carries no
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`. -/
public theorem tensorSheafSwap_comp_tensorDescentApp {W W'' : Scheme.{u}} (w : W ⟶ W'')
    (N : W''.Modules) {M : W.Modules} (ε : (Scheme.Modules.pullback w).obj N ⟶ M)
    (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj (M)).obj (M)) ⟶ M)
    (hmul : (tensorSheafSwap W.toRingedSpace M M).hom ≫ mul = mul) :
    (Scheme.Modules.pullback w).map (tensorSheafSwap W''.toRingedSpace N N).hom ≫
        tensorDescentApp w N M ε δ mul =
      tensorDescentApp w N M ε δ mul :=
  (congrArg (fun z => (Scheme.Modules.pullback w).map
        (tensorSheafSwap W''.toRingedSpace N N).hom ≫ z)
      (tensorDescentApp_eq w N M ε δ mul)).trans
    ((swapDescentChain (schemePullbackTensorIso_tensorSheafSwap w N N)
          (tensorSheafSwap_naturality W.toRingedSpace ε ε) hmul).trans
      (tensorDescentApp_eq w N M ε δ mul).symm)

/-! ### The descended multiplication is commutative -/

section Descent

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
  (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
    AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
  (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
  (hBtrans : ∀ n, Nonempty
    ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
  (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
  (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
    (AlgebraSheaf.underlyingModule (B 0)))
  (P : Stacks.Algebraization.CoherentModulesProperOver f)
  (e : (adicThickeningCompletionFunctor A I f).obj P ≅
    adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0)

/-- `AlgebraicGeometry.tensorSheafSwap_comp_tensorDescentApp` at the adic morphisms: the `n`-th
component `AlgebraicGeometry.adicAlgebraMulApp` of the descended multiplication absorbs the
inverse image of the symmetry of the tensor square of the algebraization. The commutativity input
is `AlgebraicGeometry.tensorSheafSwap_comp_multiplication` at `B n`. -/
public theorem tensorSheafSwap_comp_adicAlgebraMulApp (n : ℕ) :
    (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map
          (tensorSheafSwap X.toRingedSpace P.obj.obj P.obj.obj).hom ≫
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n =
      adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n :=
  tensorSheafSwap_comp_tensorDescentApp (pullback.fst f (adicThickeningι A I n)) P.obj.obj
    (e.hom.app n) (e.inv.app n) (multiplication (B n))
    (tensorSheafSwap_comp_multiplication (B n))

/-- **The descended multiplication is commutative, as a morphism of sheaves of modules.** If
`μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` restricts to `AlgebraicGeometry.adicAlgebraMulApp` on every adic thickening —
which is what `AlgebraicGeometry.existsUnique_multiplication_of_adicAlgebraModuleSystem`
produces — then `swap ≫ μ = μ`.

This is the uniqueness half of that existence statement: `swap ≫ μ` has the same restrictions as
`μ`, by `AlgebraicGeometry.tensorSheafSwap_comp_adicAlgebraMulApp`, and there is only one
morphism out of the tensor square with those restrictions. `CategoryTheory.Functor.map_comp` is
applied as a term and not rewritten: `simp only [Functor.map_comp]` does not fire on
`AlgebraicGeometry.Scheme.Modules.pullback`. -/
public theorem tensorSheafSwap_comp_hom_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
      (P.obj.obj)) ⟶ P.obj.obj)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n) :
    (tensorSheafSwap X.toRingedSpace P.obj.obj P.obj.obj).hom ≫ μ = μ :=
  (existsUnique_multiplication_of_adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
      hM0 P e h088F).unique
    (fun n =>
      ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map_comp
            (tensorSheafSwap X.toRingedSpace P.obj.obj P.obj.obj).hom μ).trans
        ((congrArg (fun z => (Scheme.Modules.pullback
                (pullback.fst f (adicThickeningι A I n))).map
              (tensorSheafSwap X.toRingedSpace P.obj.obj P.obj.obj).hom ≫ z) (hμ n)).trans
          (tensorSheafSwap_comp_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)))
    hμ

/-- **The `mul_comm` clause of `Stacks.FundamentalGroup.ModuleAlgebraData` for the
multiplication a cartesian system of quasi-coherent algebra sheaves descends to.** The two
previous results composed: the descended `μ` commutes with the symmetry, hence the
presheaf-level multiplication `AlgebraicGeometry.mulPresheafOfHom` it induces is commutative on
local sections.

This is one of the three laws `hdata` is owed; `mul_assoc` and `one_mul` are not proved here —
see the module docstring for what each still costs. -/
public theorem mulPresheafOfHom_comm_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
      (P.obj.obj)) ⟶ P.obj.obj)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (U : (X.Opens)ᵒᵖ) (x y : P.obj.obj.val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom P.obj.obj μ) U (x ⊗ₜ[Γ(X, U.unop)] y) =
      PresheafOfModules.Hom.app (mulPresheafOfHom P.obj.obj μ) U (y ⊗ₜ[Γ(X, U.unop)] x) :=
  mulPresheafOfHom_comm P.obj.obj μ
    (tensorSheafSwap_comp_hom_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e
      h088F μ hμ) U x y

end Descent

end AlgebraicGeometry

end
