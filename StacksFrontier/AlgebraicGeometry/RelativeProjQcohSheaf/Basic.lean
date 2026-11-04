module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent sheaves on relative Proj: the sheaf attached to a quadruple

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN).
Tag 01O6 attaches to a quadruple `(d, f : T → S, L, ψ)` over a scheme `T`, as in Section 01NS,
the `𝒪_T`-module

`ℳ̃_T = (f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n}))₀`,

the degree-zero part of the tensor product of the graded `f^*𝒜^{(d)}`-modules `f^*ℳ^{(d)}` and
`⨁_{n ∈ ℤ} L^{⊗ n}`, the latter a graded `f^*𝒜^{(d)}`-algebra through `ψ`. This file constructs
that module.

The degree-`i` piece of a Veronese regrading `𝒜^{(d)}` is `𝒜_{id}`, so the pure tensors of
total degree zero form `⨁_{n ∈ ℤ} f^*ℳ_{nd} ⊗ L^{⊗ (-n)}`, and the degree-zero part of the
tensor product over `f^*𝒜^{(d)}` is the quotient of that direct sum by the balancing relations
`(x · a) ⊗ l = x ⊗ (ψ(a) · l)`, one for each pair of degrees. The quotient is realized as the
cokernel of a single morphism out of the direct sum of the bidegreewise relation summands.

## Main definitions

* `SheafOfModules.GradedModule.smulSheaf`: the action `ℳ_n ⊗ 𝒜_i ⟶ ℳ_{n+i}` of a sheaf of
  graded algebras on a right graded module, as a morphism out of the tensor product sheaf. This
  is the module counterpart of `SheafOfModules.GradedAlgebra.mulSheaf`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting`: the map `ψ` of a quadruple, as a
  multiplicative, unit-preserving family `f^*𝒜_{id} ⟶ L^{⊗ i}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.act`: the pulled-back action
  `f^*ℳ_{nd} ⊗ f^*𝒜_{id} ⟶ f^*ℳ_{(n+i)d}` of `f^*𝒜^{(d)}` on `f^*ℳ^{(d)}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summand` and `relationSummand`,
  `relationLeft`, `Twisting.relationRight`, `Twisting.relation`: the degreewise pure tensors,
  the bidegreewise sources of the balancing relations, and the two sides of a relation.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.associatedSheaf`: **the module
  `ℳ̃_T` of Tag 01O6**, and `Twisting.pureTensor` the degreewise pure tensors inside it.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.relationLeft_pureTensor`: the pure
  tensors inside `ℳ̃_T` are balanced over `f^*𝒜^{(d)}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.existsUnique_hom`: a morphism out of
  `ℳ̃_T` is the same thing as a balanced family of morphisms out of the degreewise pure tensors.
  This universal property is what identifies the cokernel as the degree-zero part of the tensor
  product over `f^*𝒜^{(d)}`.

## Implementation notes

The target `⨁_{n ∈ ℤ} L^{⊗ n}` of `ψ` involves the negative tensor powers of `L`, so it is not
the tensor algebra `⨁_{n ≥ 0} L^{⊗ n}`; it is the Laurent algebra
`Stacks.SheafOfModules.TensorPower.laurentAlgebra` built from the coherent multiplication of
Tag 01CU. The source states `ψ` with target the tensor algebra and composes it in; the two
carry the same information, since the Laurent algebra agrees with the tensor algebra in
nonnegative degrees.

Surjectivity of the degree-one component of `ψ`, which Section 01NS also requires of a
quadruple, is deliberately **not** assumed: the formula of Tag 01O6 does not use it, so
assuming it would only weaken every statement here. The Veronese regrading is likewise not
built as a bundled graded algebra: only its homogeneous pieces `𝒜_{id}` and `ℳ_{nd}` and the
action between them occur in the formula, and they are indexed directly.

Everything is stated for the morphism of ringed spaces underlying a morphism of schemes, which
is the spelling in which the repository has the pullback of sheaves of modules
(`Stacks.PullbackTensorCoherence.pullbackFunctor`), its monoidality for the tensor product
sheaf of Tag 01CA and the comparison `f^*(X ⊗ Y) ≅ f^*X ⊗ f^*Y` of Tag 01CD. The abelian
structure and the coproducts, on the other hand, are available at Mathlib's
`AlgebraicGeometry.Scheme.Modules` spelling; `modulesAbelian` and `modulesHasCoproducts`
transport them, which is possible because the two types are equal by `rfl`.

## References

* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory PresheafOfModules

open scoped TensorProduct

universe v u w

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  {A : GradedAlgebra.{w, w} (Sheaf.toRingCat J Osharp)}
  (M : GradedModule.{w, w, w} A)

/-- The action `M_n × A_i → M_{n+i}` of a sheaf of graded algebras on a right graded module,
packaged as a bilinear map of the underlying sheaves of modules. -/
def smulBilinear (n i : ℤ) :
    SheafOfModules.BilinearMap (M.piece n) (A.piece i) (M.piece (n + i)) where
  app := M.smul n i
  map_smul_left := M.smul_smul_left n i
  map_smul_right := M.smul_smul_right n i
  naturality := M.smul_naturality n i

/-- The action in degrees `n` and `i`, as a morphism out of the objectwise tensor product of the
underlying presheaves of modules. -/
def smulPresheaf (n i : ℤ) :
    PresheafOfModules.tensorObj (M.piece n).val (A.piece i).val ⟶ (M.piece (n + i)).val :=
  PresheafOfModules.ofBilinear (M.smulBilinear n i)

/-- On a pure tensor `x ⊗ₜ y` of sections over `U`, `smulPresheaf` is the action `x • y`. -/
@[simp]
theorem smulPresheaf_tmul (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    PresheafOfModules.Hom.app (M.smulPresheaf n i) U (x ⊗ₜ y) = M.smul n i U x y :=
  PresheafOfModules.ofBilinear_tmul (M.smulBilinear n i) U x y

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The action in degrees `n` and `i` as a morphism of sheaves of modules
`M_n ⊗ A_i ⟶ M_{n+i}` out of the tensor product sheaf, induced by the bilinear map
`smulBilinear`; the module counterpart of `SheafOfModules.GradedAlgebra.mulSheaf`. -/
def smulSheaf (n i : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj (M.piece n)).obj
      (A.piece i) ⟶ M.piece (n + i) :=
  tensorSheafDesc (M.smulPresheaf n i)

/-- On the image in the tensor product sheaf of a pure tensor `x ⊗ₜ y` of sections over `U`,
`smulSheaf` is the action `x • y`. -/
@[simp]
theorem smulSheaf_unit (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (M.smulSheaf n i).val.app U
        ((tensorSheafUnit (M.piece n) (A.piece i)).app U (x ⊗ₜ y)) = M.smul n i U x y :=
  (tensorSheafDesc_unit (M.smulPresheaf n i) U x y).trans (M.smulPresheaf_tmul n i U x y)

end SheafOfModules.GradedModule

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-- Sheaves of modules on the ringed space of a scheme form an abelian category. This is the
instance of `AlgebraicGeometry.Scheme.Modules`, transported to the spelling
`Stacks.RingedSpace.structureRingSheaf` that the ringed-space pullback and the monoidal
structure of Tag 01CA use; the two types are equal by `rfl`. -/
@[instance_reducible]
def modulesAbelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :=
  inferInstanceAs (Abelian X.Modules)

/-- Sheaves of modules on the ringed space of a scheme have coproducts indexed by any type in
the lowest universe, transported to the `Stacks.RingedSpace.structureRingSheaf` spelling. -/
theorem modulesHasCoproducts (X : Scheme.{u}) :
    HasCoproducts.{0} (SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :=
  inferInstanceAs (HasCoproducts.{0} X.Modules)

attribute [local instance] modulesAbelian modulesHasCoproducts

variable {T S : Scheme.{u}}

/-- The morphism of ringed spaces underlying a morphism of schemes. -/
abbrev ringedSpaceHom (f : T ⟶ S) : T.toRingedSpace ⟶ S.toRingedSpace := f.toLRSHom.toShHom

/-- The sheaf condition on the structure presheaf of the ringed space of a scheme, in the form
the monoidal structure of Tag 01CA and the Laurent algebra take as an argument. -/
abbrev isSheafStruct (X : Scheme.{u}) :=
  (structureSheafRing X.toRingedSpace).property

variable (f : T ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
  (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of all integral tensor powers of `L`, as a sheaf of
`ℤ`-graded `𝒪_T`-algebras. This is the target of the map `ψ` of a quadruple; it is not the
tensor algebra `⨁_{n ≥ 0} L^{⊗ n}`, because the formula of Tag 01O6 involves the negative
tensor powers as well. -/
abbrev laurent : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace) :=
  laurentAlgebra T.toRingedSpace.presheaf (isSheafStruct T) L

/-- **The map `ψ` of a quadruple `(d, f : T → S, L, ψ)` of Section 01NS**: a homomorphism of
sheaves of graded algebras from the pullback `f^*𝒜^{(d)}` of the `d`-th Veronese regrading of
`𝒜` to the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of `L`.

The degree-`i` piece of `𝒜^{(d)}` is `𝒜_{id}`, so the homogeneous components are the morphisms
`f^*𝒜_{id} ⟶ L^{⊗ i}`. The source states `ψ` with target the tensor algebra
`⨁_{n ≥ 0} L^{⊗ n}` and composes it into the Laurent algebra; the two formulations carry the
same information, since the Laurent algebra agrees with the tensor algebra in nonnegative
degrees.

The surjectivity of the degree-one component, which Section 01NS also requires of a quadruple,
is **not** assumed: the formula of Tag 01O6 does not use it, so assuming it would only weaken
every statement below. -/
structure Twisting where
  /-- The homogeneous components `f^*𝒜_{id} ⟶ L^{⊗ i}` of `ψ`. -/
  app (i : ℤ) : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i
  /-- `ψ` is multiplicative: it carries the multiplication of `f^*𝒜^{(d)}`, i.e. the pullback of
  the multiplication of `𝒜`, to the multiplication of the Laurent algebra. -/
  app_mul (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        app (i + j)
  /-- `ψ` preserves the distinguished degree-zero unit. -/
  app_one :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L)

/-- The pulled-back action `f^*ℳ_{nd} ⊗ f^*𝒜_{id} ⟶ f^*ℳ_{(n+i)d}` of `f^*𝒜^{(d)}` on
`f^*ℳ^{(d)}`: the pullback of the action of `𝒜` on `ℳ`, read through the comparison
`f^*(X ⊗ Y) ≅ f^*X ⊗ f^*Y` of Tag 01CD. -/
def act {T S : Scheme.{u}} (f : T ⟶ S)
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ) (n i : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)) ⊗
        (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶
      (pullbackFunctor (ringedSpaceHom f)).obj (M.piece ((n + i) * d)) :=
  inv (pullbackTensorComparison (ringedSpaceHom f) (M.piece (n * d)) (A.piece (i * d))) ≫
    (pullbackFunctor (ringedSpaceHom f)).map
      (M.smulSheaf (n * d) (i * d) ≫
        eqToHom (congrArg M.piece (by ring : n * d + i * d = (n + i) * d)))

/-- The degree-`n` summand `f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` of the pure tensors of total degree zero. -/
def summand {T S : Scheme.{u}} (f : T ⟶ S)
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (n : ℤ) :
    SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  (pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)) ⊗ (laurent L).piece (-n)

/-- The summand `(f^*ℳ_{nd} ⊗ f^*𝒜_{id}) ⊗ L^{⊗ (-(n+i))}` carrying the balancing relations in
bidegree `(n, i)`. -/
def relationSummand {T S : Scheme.{u}} (f : T ⟶ S)
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (p : ℤ × ℤ) : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ⊗
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d))) ⊗
    (laurent L).piece (-(p.1 + p.2))

/-- One side of a balancing relation: `(x, a, l) ↦ (x · a) ⊗ l`. It does not involve `ψ`. -/
def relationLeft {T S : Scheme.{u}} (f : T ⟶ S)
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (p : ℤ × ℤ) : relationSummand f M d L p ⟶ summand f M d L (p.1 + p.2) :=
  MonoidalCategoryStruct.whiskerRight (act f M d p.1 p.2) ((laurent L).piece (-(p.1 + p.2)))

namespace Twisting

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f A d L)

/-- The other side of a balancing relation: `(x, a, l) ↦ x ⊗ (ψ(a) · l)`. -/
def relationRight (p : ℤ × ℤ) : relationSummand f M d L p ⟶ summand f M d L p.1 :=
  (α_ _ _ _).hom ≫
    MonoidalCategoryStruct.whiskerLeft
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
      (MonoidalCategoryStruct.whiskerRight (ψ.app p.2) ((laurent L).piece (-(p.1 + p.2))) ≫
        (laurent L).mulSheaf p.2 (-(p.1 + p.2)) ≫
          eqToHom (congrArg (laurent L).piece (by ring : p.2 + -(p.1 + p.2) = -p.1)))

/-- **The balancing relations of the tensor product over `f^*𝒜^{(d)}`**, as a single morphism
from the direct sum of the bidegreewise relation summands to the direct sum of the degreewise
pure tensors: in bidegree `(n, i)` it is the difference `(x · a) ⊗ l - x ⊗ (ψ(a) · l)`. -/
def relation : (∐ relationSummand f M d L) ⟶ (∐ summand f M d L) :=
  Sigma.desc fun p =>
    (relationLeft f M d L p ≫ Sigma.ι (summand f M d L) (p.1 + p.2)) -
      (relationRight M ψ p ≫ Sigma.ι (summand f M d L) p.1)

/-- **Stacks Project, Tag 01O6, equation (27.17.0.1).** The `𝒪_T`-module

`ℳ̃_T = (f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n}))₀`

attached to a graded `𝒜`-module `ℳ` and a quadruple `(d, f : T → S, L, ψ)`: the degree-zero
part of the tensor product, over the pullback of the `d`-th Veronese regrading of `𝒜`, of the
pullback of the `d`-th Veronese regrading of `ℳ` with the Laurent algebra of `L`. It is the
quotient of `⨁_{n ∈ ℤ} f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` by the balancing relations
`(x · a) ⊗ l = x ⊗ (ψ(a) · l)`. -/
@[stacks 01O6]
def associatedSheaf : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  cokernel (relation M ψ)

/-- The degree-`n` pure tensors `x ⊗ l`, with `x` a local section of `f^*ℳ_{nd}` and `l` one of
`L^{⊗ (-n)}`, inside `ℳ̃_T`. -/
def pureTensor (n : ℤ) : summand f M d L n ⟶ associatedSheaf M ψ :=
  Sigma.ι (summand f M d L) n ≫ cokernel.π (relation M ψ)

/-- The component of the relation morphism in bidegree `(n, i)`. -/
theorem ι_relation (p : ℤ × ℤ) :
    Sigma.ι (relationSummand f M d L) p ≫ relation M ψ =
      relationLeft f M d L p ≫ Sigma.ι (summand f M d L) (p.1 + p.2) -
        relationRight M ψ p ≫ Sigma.ι (summand f M d L) p.1 :=
  Sigma.ι_desc _ _

/-- **The pure tensors are balanced over `f^*𝒜^{(d)}`**: inside `ℳ̃_T` a homogeneous local
section of `f^*𝒜^{(d)}` may be moved across the tensor sign. -/
theorem relationLeft_pureTensor (p : ℤ × ℤ) :
    relationLeft f M d L p ≫ pureTensor M ψ (p.1 + p.2) =
      relationRight M ψ p ≫ pureTensor M ψ p.1 := by
  have h : (Sigma.ι (relationSummand f M d L) p ≫ relation M ψ) ≫
      cokernel.π (relation M ψ) = 0 := by
    rw [Category.assoc, cokernel.condition, comp_zero]
  rw [ι_relation, Preadditive.sub_comp] at h
  have h' := sub_eq_zero.mp h
  dsimp only [pureTensor, associatedSheaf]
  rw [← Category.assoc, ← Category.assoc]
  exact h'

/-- **`ℳ̃_T` is the universal recipient of a balanced family of degreewise maps.** A morphism out
of `ℳ̃_T` is the same thing as a family of morphisms out of the degreewise pure tensors which
satisfies every balancing relation; this is what identifies the quotient above as the
degree-zero part of the tensor product over `f^*𝒜^{(d)}`. -/
theorem existsUnique_hom (N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (b : ∀ n : ℤ, summand f M d L n ⟶ N)
    (hb : ∀ p : ℤ × ℤ, relationLeft f M d L p ≫ b (p.1 + p.2) = relationRight M ψ p ≫ b p.1) :
    ∃! h : associatedSheaf M ψ ⟶ N, ∀ n : ℤ, pureTensor M ψ n ≫ h = b n := by
  have hzero : relation M ψ ≫ Sigma.desc b = 0 := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [comp_zero, ← Category.assoc, ι_relation, Preadditive.sub_comp, Category.assoc,
      Category.assoc, Sigma.ι_desc, Sigma.ι_desc, hb p, sub_self]
  have key : ∀ n : ℤ, pureTensor M ψ n ≫ cokernel.desc _ _ hzero = b n := by
    intro n
    dsimp only [pureTensor, associatedSheaf]
    rw [Category.assoc, cokernel.π_desc, Sigma.ι_desc]
  refine ⟨cokernel.desc _ _ hzero, key, fun h hh => ?_⟩
  refine (cancel_epi (cokernel.π (relation M ψ))).mp (Sigma.hom_ext _ _ fun n => ?_)
  simp only [← Category.assoc]
  exact (hh n).trans (key n).symm

end Twisting

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
