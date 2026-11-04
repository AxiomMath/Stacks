module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

/-!
# Base change for the relative Proj functor

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), fix an
integer `d`, and let `F_d` be the functor of strict equivalence classes of quadruples of
Section 01NS. For a morphism of base schemes `g : S' ⟶ S` put `𝒜' = g^*𝒜` and let `F'_d` be the
functor of `(S', 𝒜')`. Tag 01NT asserts a canonical isomorphism
`F'_d ≅ h_{S'} ×_{h_S} F_d` of functors on `Sch^{opp}`.

The whole of the source's proof is one identification. A quadruple `(d, f' : T → S', L, ψ')`
for `(S', 𝒜')` and a quadruple `(d, f, L, ψ)` for `(S, 𝒜)` together with a factorization
`f = g ∘ f'` carry the same data, because

`(f')^*(𝒜')^{(d)} = (f')^*g^*(𝒜^{(d)}) = f^*𝒜^{(d)}`,

and `L` and `ψ` are simply carried across. This file **constructs** that identification: it is
`Stacks.PullbackCompMonoidal.comparisonIso`, which is an isomorphism — not an isomorphism
obtained from an existence statement, and not a `Nonempty` — and the bijection it induces on
the degreewise components of the map `ψ` of a quadruple is constructed from it.

Note that base change moves only the **source** of `ψ`. The invertible module `L` of a
quadruple lives on the test scheme `T`, which does not move, so the Laurent algebra
`⨁_{n ∈ ℤ} L^{⊗ n}` that is the target of `ψ` is literally the same object on both sides. This
is why the identification above is all that the correspondence of quadruples needs.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebra`: **the base-changed graded
  algebra `𝒜' = g^*𝒜`** of Tag 01NT, the degreewise pullback of `𝒜` along `g` with the pulled
  back multiplication and unit.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseBaseChangeIso`: **the canonical
  isomorphism `f^*𝒜^{(d)}_n ≅ (f')^*(𝒜')^{(d)}_n` of Tag 01NT**, where `f = g ∘ f'`. This is
  the identification the source's proof is, constructed.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.twistingAppEquiv`: **the canonical bijection
  between the degreewise components of a map `ψ'` for `(S', 𝒜')` and those of a map `ψ` for
  `(S, 𝒜)`** over the composite morphism, induced by `veroneseBaseChangeIso`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseBaseChangeIso_tensor` and
  `veroneseBaseChangeIso_unit`: the canonical isomorphism is compatible with the comparison of
  Tag 01CD and with the structure-sheaf comparison, in the degrees the Veronese regrading
  uses. These are the multiplicativity and unitality of the identification, for the monoidal
  structure whose tensorator is the comparison of Tag 01CD.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.twistingAppEquiv_apply` and
  `twistingAppEquiv_symm_apply`: the bijection is the one the source writes, namely
  precomposition with the canonical identification in each degree.

## Implementation notes

`𝒜' = g^*𝒜` is taken **literally**: `baseAlgebra g 𝒜` is the pulled-back sheaf of graded
algebras, so no hypothesis relating `𝒜'` to `𝒜` is assumed anywhere below. A formulation that
instead took a degreewise comparison of `𝒜'` with `g^*𝒜` as a hypothesis, with its
compatibility with multiplication and unit among the hypotheses, would be assuming what
`veroneseBaseChangeIso_tensor` and `veroneseBaseChangeIso_unit` prove.

Of the two pullbacks of a sheaf of graded algebras in the repository the one used here is
`Stacks.RingedSpace.pullbackGradedAlgebra`, whose multiplication is the pulled-back **bilinear
map on sections** and which is characterised by
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit`. The other,
`Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra`, has the same pieces but takes its
multiplication from `Stacks.PullbackGradedAlgebra.pullbackMul`, i.e. from the monoidal
structure `pullbackStrictMonoidal`; see "Not done here".

The two spellings `ringedSpaceHom f' ≫ ringedSpaceHom g` and `ringedSpaceHom (f' ≫ g)` of the
morphism of ringed spaces underlying the composite are equal by `rfl`, so
`veroneseBaseChangeIso` is stated at the second, which is the one a quadruple over `f' ≫ g` is
indexed by, and `Stacks.PullbackCompMonoidal.comparisonIso` is accepted at it directly.

## Not done here

* **The isomorphism of functors is not constructed here**, and neither is the induced bijection
  on quadruples. Both are built from the material of this file in
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeFunctor`: the bijection of
  quadruples is `...BaseChangeFunctor.Quadruple.baseChangeEquiv` and the isomorphism of functors
  is `...BaseChangeFunctor.Fd.isLimitBaseChangeCone` together with
  `...BaseChangeFunctor.Fd.baseChangePullbackIso`. The two inputs that construction needs beyond
  what is proved here are the identification of the multiplication and of the unit of
  `baseAlgebra g 𝒜` with the pullbacks of those of `𝒜` through the comparison of Tag 01CD and
  through the structure-sheaf comparison, which are `...BaseChangeFunctor.baseMul_eq` and
  `baseOne_eq`; they are proved on the pullback-unit images of the local sections, by
  `Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext` and `pullback_hom_ext`, so neither
  the multiplicativity of the comparison on stalks for an iterated pullback nor the
  identification of the tensorator of
  `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` with the inverse of the comparison of
  Tag 01CD — which `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` still
  records as an open dedup — is needed.
* No universe generality beyond `Scheme.{u}` with modules in `u`, inherited from
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple` and ultimately from
  `RingedSpaceModuleAdjunction.modulePullback`. Nothing is narrowed relative to the imports.
* Quasi-coherence of `𝒜` is not used, exactly as in Section 01NS's treatment of quadruples.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S S' T : Scheme.{u}}

/-- **Stacks Project, Tag 01NT.** The base-changed graded algebra `𝒜' = g^*𝒜` along a morphism
`g : S' ⟶ S` of base schemes: its homogeneous pieces are the pullbacks of those of `𝒜`, and its
multiplication and unit are the pullbacks of those of `𝒜`. -/
def baseAlgebra (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace) :=
  Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom g) A

/-- The degree `n` piece of `g^*𝒜` is the pullback `g^*𝒜_n` of the degree `n` piece of `𝒜`. -/
@[simp] theorem baseAlgebra_piece (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (n : ℤ) :
    (baseAlgebra g A).piece n = (pullbackFunctor (ringedSpaceHom g)).obj (A.piece n) :=
  rfl

/-- **Stacks Project, Tag 01NT, the canonical identification.** For `g : S' ⟶ S` and
`f' : T ⟶ S'` the canonical isomorphism

`f^*𝒜^{(d)}_n ≅ (f')^*(𝒜')^{(d)}_n`,  where `f = g ∘ f'` and `𝒜' = g^*𝒜`,

in each degree `n`. Unwinding the Veronese regrading this is the identification
`(g ∘ f')^*𝒜_{nd} ≅ (f')^*(g^*𝒜_{nd})`, which is the contraction of an iterated pullback; the
source writes it as `(f')^*(𝒜')^{(d)} = (f')^*g^*(𝒜^{(d)}) = f^*𝒜^{(d)}`.

It is **constructed**, from `Stacks.PullbackCompMonoidal.comparisonIso`. -/
def veroneseBaseChangeIso (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d n : ℤ) :
    (pullbackFunctor (ringedSpaceHom (f' ≫ g))).obj (A.piece (n * d)) ≅
      (pullbackFunctor (ringedSpaceHom f')).obj ((baseAlgebra g A).piece (n * d)) :=
  Stacks.PullbackCompMonoidal.comparisonIso (ringedSpaceHom g) (ringedSpaceHom f')
    (A.piece (n * d))

/-- The canonical identification of Tag 01NT is compatible with the comparison of Tag 01CD:
contracting the iterated pullback of a tensor product of two Veronese pieces and then splitting
the product agrees with splitting first and contracting each factor.

This is the multiplicativity of the identification, for the monoidal structure of `f^*` whose
tensorator is the comparison of Tag 01CD. -/
theorem veroneseBaseChangeIso_tensor (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (d i j : ℤ) :
    Stacks.PullbackCompMonoidal.comparison (ringedSpaceHom g) (ringedSpaceHom f')
          (A.piece (i * d) ⊗ A.piece (j * d)) ≫
        (pullbackFunctor (ringedSpaceHom f')).map
            (pullbackTensorComparison (ringedSpaceHom g) (A.piece (i * d))
              (A.piece (j * d))) ≫
          pullbackTensorComparison (ringedSpaceHom f')
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)))
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d))) =
      pullbackTensorComparison (ringedSpaceHom (f' ≫ g)) (A.piece (i * d))
          (A.piece (j * d)) ≫
        ((veroneseBaseChangeIso g f' A d i).hom ⊗ₘ
          (veroneseBaseChangeIso g f' A d j).hom) :=
  Stacks.PullbackCompMonoidal.comparison_tensor (ringedSpaceHom g) (ringedSpaceHom f')
    (A.piece (i * d)) (A.piece (j * d))

/-- The canonical identification of Tag 01NT is compatible with the structure-sheaf comparison:
contracting the iterated pullback of the unit object and then comparing twice with the structure
sheaf agrees with comparing once along the composite.

This is the unitality of the identification, for the monoidal structure of `f^*` whose unit
morphism is the structure-sheaf comparison. -/
theorem veroneseBaseChangeIso_unit (g : S' ⟶ S) (f' : T ⟶ S') :
    Stacks.PullbackCompMonoidal.comparison (ringedSpaceHom g) (ringedSpaceHom f')
          (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
        (pullbackFunctor (ringedSpaceHom f')).map
            (pullbackUnitComparison (ringedSpaceHom g)) ≫
          pullbackUnitComparison (ringedSpaceHom f') =
      pullbackUnitComparison (ringedSpaceHom (f' ≫ g)) :=
  Stacks.PullbackCompMonoidal.comparison_unit (ringedSpaceHom g) (ringedSpaceHom f')

/-- **Stacks Project, Tag 01NT.** The canonical bijection between the degreewise components of
a map `ψ' : (f')^*(𝒜')^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` for the base-changed situation `(S', 𝒜')` and
those of a map `ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` for `(S, 𝒜)` over the composite
`f = g ∘ f'`.

This is the source's `ψ = ψ'`: in each degree the component is carried across the canonical
identification `veroneseBaseChangeIso`, and nothing else happens — the invertible module `L` and
its Laurent algebra live on the test scheme and are not moved by the base change. -/
def twistingAppEquiv (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] :
    (∀ i : ℤ, (pullbackFunctor (ringedSpaceHom f')).obj
          ((baseAlgebra g A).piece (i * d)) ⟶ (laurent L).piece i) ≃
      (∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (f' ≫ g))).obj (A.piece (i * d)) ⟶
        (laurent L).piece i) where
  toFun φ i := (veroneseBaseChangeIso g f' A d i).hom ≫ φ i
  invFun ψ i := (veroneseBaseChangeIso g f' A d i).inv ≫ ψ i
  left_inv _ := funext fun _ => Iso.inv_hom_id_assoc _ _
  right_inv _ := funext fun _ => Iso.hom_inv_id_assoc _ _

/-- The degree `i` component of `twistingAppEquiv g f' A d L φ` is `φ i` precomposed with the
canonical identification `veroneseBaseChangeIso g f' A d i`. -/
@[simp] theorem twistingAppEquiv_apply (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (φ : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom f')).obj
      ((baseAlgebra g A).piece (i * d)) ⟶ (laurent L).piece i) (i : ℤ) :
    twistingAppEquiv g f' A d L φ i = (veroneseBaseChangeIso g f' A d i).hom ≫ φ i :=
  rfl

/-- The degree `i` component of `(twistingAppEquiv g f' A d L).symm ψ` is `ψ i` precomposed with
the inverse of the canonical identification `veroneseBaseChangeIso g f' A d i`. -/
@[simp] theorem twistingAppEquiv_symm_apply (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    (ψ : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (f' ≫ g))).obj (A.piece (i * d)) ⟶
      (laurent L).piece i) (i : ℤ) :
    (twistingAppEquiv g f' A d L).symm ψ i = (veroneseBaseChangeIso g f' A d i).inv ≫ ψ i :=
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
