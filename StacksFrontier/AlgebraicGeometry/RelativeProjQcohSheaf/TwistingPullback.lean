module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullbackMultiplication
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Union

/-!
# Pulling back the map `ψ` of a quadruple along a morphism of test schemes

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to
each `d ≥ 1` the quadruples `(d, f : T → S, L, ψ)` over a test scheme `T`, and the display 01NX
assembles their classes into `F(T) = ⋃_{d ≥ 1} F_d(T)`. Tag 01NY asserts that `F` is
representable by a scheme.

Representability is a statement about a **functor**, and in this repository `F` is only the
family of its values: `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F` is defined on each test
scheme separately, because the pullback of a quadruple along a morphism `g : T' ⟶ T` of test
schemes was not available. Three sibling modules record that absence as the reason — the
implementation notes of `...RelativeProjQcohSheaf.Quadruple`,
`...RelativeProjQcohSheaf.BaseChange` and `...RelativeProjQcohSheaf.Union` — and each names the
same two missing inputs: the comparison `g^*(L^{⊗ n}) ≅ (g^*L)^{⊗ n}` of the **integral** tensor
powers of Tag 01CU compatibly with the coherent multiplication, and the comparison
`(g ∘ f)^* ≅ g^* ∘ f^*` of pullbacks of sheaves of modules.

Both are now available: the first is `Stacks.TensorPowerPullback.pullbackIntPowIso` with its
multiplicativity `Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`, the second is
`Stacks.PullbackCompMonoidal.comparison` with its compatibility
`Stacks.PullbackCompMonoidal.comparison_tensor`. This file puts them together and pulls the map
`ψ` of a quadruple back along `g`, **multiplicatively in every pair of integer degrees**, which
is every field of a map of quadruples over `g ≫ f` except the unit normalisation.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentMul`: the coherent multiplication
  `L^{⊗ i} ⊗ L^{⊗ j} ⟶ L^{⊗ (i + j)}` of Tag 01CU, ascribed at the spelling the Laurent algebra
  of Section 01NS is graded by.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback`: the comparison
  `g^*(L^{⊗ i}) ⟶ (g^*L)^{⊗ i}` of Tag 01CU, likewise ascribed.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison`: the comparison
  `(g ∘ f)^*M ⟶ g^*(f^*M)` of `Stacks.PullbackCompMonoidal.comparison`, ascribed at the spelling
  a quadruple over `g ≫ f` is indexed by.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp`: **the degreewise
  pullback of the map `ψ` of a quadruple along a morphism `g : T' ⟶ T` of test schemes**, the
  family of morphisms `(g ∘ f)^*𝒜_{id} ⟶ (g^*L)^{⊗ i}`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent_mulSheaf_eq`: the multiplication of the
  Laurent algebra of an invertible module, as a morphism out of the tensor product sheaf, is the
  coherent multiplication of Tag 01CU. This is the bridge between the vocabulary a `Twisting` is
  stated in and the vocabulary the multiplicativity of the tensor-power pullback is stated in.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_mul`: the comparison of the
  integral tensor powers is multiplicative, in that vocabulary.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_mul`: **the pullback of
  `ψ` is multiplicative in every pair of integer degrees**, exactly the condition
  `Twisting.app_mul` demands of the map `ψ` of a quadruple over `g ≫ f`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.epi_pullbackApp`: the pullback of `ψ`
  keeps a surjective homogeneous component surjective, which is the remaining condition
  `Quadruple.epi_app_one` demands.

## Implementation notes

The homogeneous pieces of the Laurent algebra are spelled through
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` while the pullback of sheaves of
modules is spelled through `Stacks.RingedSpace.structureRingSheaf`; the two are equal by `rfl`
and are not syntactically equal, so a term mixing them is not type-correct at `implicit`
transparency and `rw` refuses any goal containing it, reporting a pattern rather than the cause.
The cure prescribed in this directory and in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal` is a `def` with an
**ascribed** type: `laurentMul`, `laurentPullback` and `compComparison` are the three crossings,
each made once inside a proof given by `:=`, and every statement below is written with them. The
same applies to the two spellings `ringedSpaceHom g ≫ ringedSpaceHom f` and
`ringedSpaceHom (g ≫ f)` of the morphism of ringed spaces underlying a composite, which is why
`compComparison` is ascribed at the second.

`pullbackTensorComparison_naturality_tensorHom` is the naturality of the comparison of Tag 01CD
in both variables at once. The repository has the two whiskered halves; the monoidal tensor
product of two morphisms is their composite by `MonoidalCategory.tensorHom_def`, which is how the
two halves combine.

## Not done here

* **The pullback of a *quadruple* is not constructed here.** The remaining field of
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting`, the unit normalisation `app_one`, is
  stated through `Stacks.PullbackGradedAlgebra.pullbackOne`, which is the unit morphism of the
  monoidal structure `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` on `f^*` composed with
  the unit of `𝒜`; transporting it along `g` is the unit coherence of `compComparison` for that
  structure, whereas `Stacks.PullbackCompMonoidal.comparison_unit` proves the coherence for the
  structure-sheaf comparison `Stacks.PullbackTensorCoherence.pullbackUnitComparison` of Tag 01CD.
  The two are identified in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit`, and
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback` uses that to transport
  `app_one` and to build `Quadruple.pullback`. Only the *unit* halves of the two monoidal
  structures are identified; their tensorators are still not, so the identification sought in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` and
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal` is only half closed.
* The discrepancy could not have been absorbed by correcting the degree-zero component of
  `Twisting.pullbackApp`: such a correction is an invertible endomorphism `t` of the unit object,
  and `Twisting.pullbackApp_mul` in bidegree `(0, 0)` then reads `t ⊗ t = t`, so `t` is trivial.
  This remark is not formalised; it explains why no such correction is made.
* **`F` is a functor**, `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.functor` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`, whose map on morphisms is
  the `F(T) → F(T')` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback`. What is *not* proved is
  the representability of `F` by a scheme, nor the identification of that scheme with the
  relative Proj of `𝒜`: neither half of a representability statement — the functor-of-points
  comparison and its bijectivity — is stated.
* The surjectivity of the degree-one component of `ψ`, which Section 01NS requires of a
  quadruple, plays no part in the multiplicativity below; it is transported separately, by
  `Twisting.epi_pullbackApp`.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
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

/-- **The coherent multiplication `L^{⊗ i} ⊗ L^{⊗ j} ⟶ L^{⊗ (i + j)}` of Tag 01CU**, ascribed at
the spelling the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of Section 01NS is graded by. -/
def laurentMul {T : Scheme.{u}} (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (i j : ℤ) :
    (laurent L).piece i ⊗ (laurent L).piece j ⟶ (laurent L).piece (i + j) :=
  (coherentMulIso T.toRingedSpace.presheaf (isSheafStruct T) L i j).hom

/-- **The multiplication of the Laurent algebra is the coherent multiplication of Tag 01CU.**
`SheafOfModules.GradedAlgebra.mulSheaf` is the morphism out of the tensor product sheaf that a
bilinear multiplication of local sections descends to, and the multiplication of
`Stacks.SheafOfModules.TensorPower.laurentAlgebra` was read off from
`Stacks.SheafOfModules.TensorPower.coherentMulIso`; so the two agree.

This is the bridge the pullback of a map `ψ` needs: `Twisting.app_mul` is stated with `mulSheaf`
and the multiplicativity of the tensor-power pullback with `coherentMulIso`. -/
theorem laurent_mulSheaf_eq {T : Scheme.{u}}
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (i j : ℤ) :
    (laurent L).mulSheaf i j = laurentMul L i j :=
  tensor_hom_ext fun U x y =>
    (SheafOfModules.GradedAlgebra.mulSheaf_unit (laurent L) i j U x y).trans
      (mulBilinear_app T.toRingedSpace.presheaf (isSheafStruct T) L i j U x y)

/-- **Naturality of the comparison of Tag 01CD in both variables at once**: it carries the
pullback of a tensor product of two morphisms to the tensor product of their pullbacks. The
repository has the two whiskered halves, and a monoidal tensor product of morphisms is their
composite. -/
theorem pullbackTensorComparison_naturality_tensorHom {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    {A A' B B' : SheafOfModules.{u} (structureRingSheaf Y)} (u : A ⟶ A') (v : B ⟶ B') :
    (pullbackFunctor h).map (u ⊗ₘ v) ≫ pullbackTensorComparison h A' B' =
      pullbackTensorComparison h A B ≫
        ((pullbackFunctor h).map u ⊗ₘ (pullbackFunctor h).map v) := by
  rw [tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc,
    pullbackTensorComparison_naturality_right, ← Category.assoc,
    pullbackTensorComparison_naturality_left, Category.assoc, ← tensorHom_def]

variable {T' T S : Scheme.{u}}

/-- **The comparison `(g ∘ f)^*M ⟶ g^*(f^*M)` of an iterated pullback**, ascribed at the
spelling `ringedSpaceHom (g ≫ f)` of the composite that a quadruple over `g ≫ f` is indexed by.
It is `Stacks.PullbackCompMonoidal.comparison`; the ascription is what makes a goal mentioning it
type-correct at `implicit` transparency. -/
def compComparison (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj M ⟶
      (pullbackFunctor (ringedSpaceHom g)).obj
        ((pullbackFunctor (ringedSpaceHom f)).obj M) :=
  Stacks.PullbackCompMonoidal.comparison (ringedSpaceHom f) (ringedSpaceHom g) M

/-- The comparison `(g ∘ f)^*M ⟶ g^*(f^*M)` of an iterated pullback is an isomorphism. -/
instance isIso_compComparison (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    IsIso (compComparison g f M) :=
  Stacks.PullbackCompMonoidal.isIso_comparison (ringedSpaceHom f) (ringedSpaceHom g) M

/-- Naturality of the comparison of an iterated pullback, at the ascribed spelling. -/
theorem compComparison_naturality (g : T' ⟶ T) (f : T ⟶ S)
    {M N : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)} (φ : M ⟶ N) :
    compComparison g f M ≫ (pullbackFunctor (ringedSpaceHom g)).map
          ((pullbackFunctor (ringedSpaceHom f)).map φ) =
      (pullbackFunctor (ringedSpaceHom (g ≫ f))).map φ ≫ compComparison g f N :=
  Stacks.PullbackCompMonoidal.comparison_naturality (ringedSpaceHom f) (ringedSpaceHom g) φ

/-- The comparison of an iterated pullback is compatible with the comparison of Tag 01CD, at the
ascribed spelling. -/
theorem compComparison_tensor (g : T' ⟶ T) (f : T ⟶ S)
    (M N : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    compComparison g f (M ⊗ N) ≫
        (pullbackFunctor (ringedSpaceHom g)).map
            (pullbackTensorComparison (ringedSpaceHom f) M N) ≫
          pullbackTensorComparison (ringedSpaceHom g)
            ((pullbackFunctor (ringedSpaceHom f)).obj M)
            ((pullbackFunctor (ringedSpaceHom f)).obj N) =
      pullbackTensorComparison (ringedSpaceHom (g ≫ f)) M N ≫
        (compComparison g f M ⊗ₘ compComparison g f N) :=
  Stacks.PullbackCompMonoidal.comparison_tensor (ringedSpaceHom f) (ringedSpaceHom g) M N

/-- **`compComparison_tensor` solved for the inverses of the comparisons of Tag 01CD.** Every
morphism occurring in `compComparison_tensor` other than the two contractions is an
isomorphism, so the compatibility can be read as an identity between the two ways of passing
from the pullback along `g ≫ f` of a tensor product to the pullback along `g` of the tensor
product of the pullbacks along `f`.

This is the form the multiplicativity law of a quadruple is stated in: there the comparison of
Tag 01CD appears inverted, as the morphism **out of** a tensor product of pullbacks. -/
theorem inv_pullbackTensorComparison_comp_compComparison (g : T' ⟶ T) (f : T ⟶ S)
    (M N : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) M N) ≫ compComparison g f (M ⊗ N) =
      (compComparison g f M ⊗ₘ compComparison g f N) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g)
            ((pullbackFunctor (ringedSpaceHom f)).obj M)
            ((pullbackFunctor (ringedSpaceHom f)).obj N)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map
            (inv (pullbackTensorComparison (ringedSpaceHom f) M N)) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← Category.assoc,
    ← compComparison_tensor g f M N]
  simp

/-- **The two comparisons move a morphism out of a tensor product across an iterated pullback.**
Given a morphism `m : M ⊗ N ⟶ K` on `S`, a morphism `a` out of its inverse image on `T` and a
morphism `l` out of the inverse image of the target on `T'`, the composite built on `T'` from
`m`, `a` and `l` using the comparison of Tag 01CD along `g ≫ f` and the contraction of the
iterated pullback agrees with the inverse image along `g` of the composite built on `T` from `m`
and `a`, conjugated by the tensor product of the two contractions and by the inverse of the
comparison of Tag 01CD along `g`.

Every object and morphism is free, which is what makes the statement usable at the two spellings
of the structure sheaf: it is `inv_pullbackTensorComparison_comp_compComparison` followed by
`compComparison_naturality`. -/
theorem inv_pullbackTensorComparison_comp_map_comp_compComparison (g : T' ⟶ T) (f : T ⟶ S)
    {M N K : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)} (m : M ⊗ N ⟶ K)
    {P : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (a : (pullbackFunctor (ringedSpaceHom f)).obj K ⟶ P)
    {Q : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    (l : (pullbackFunctor (ringedSpaceHom g)).obj P ⟶ Q) :
    inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) M N) ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).map m ≫
          compComparison g f K ≫ (pullbackFunctor (ringedSpaceHom g)).map a ≫ l =
      ((compComparison g f M ⊗ₘ compComparison g f N) ≫
          inv (pullbackTensorComparison (ringedSpaceHom g)
            ((pullbackFunctor (ringedSpaceHom f)).obj M)
            ((pullbackFunctor (ringedSpaceHom f)).obj N))) ≫
        (pullbackFunctor (ringedSpaceHom g)).map
          (inv (pullbackTensorComparison (ringedSpaceHom f) M N) ≫
            (pullbackFunctor (ringedSpaceHom f)).map m ≫ a) ≫ l := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [← compComparison_naturality g f m]
  slice_lhs 1 2 => rw [inv_pullbackTensorComparison_comp_compComparison g f M N]
  simp only [Category.assoc]

/-- **The comparison `g^*(L^{⊗ i}) ⟶ (g^*L)^{⊗ i}` of the integral tensor powers of Tag 01CU**,
ascribed at the spelling the Laurent algebra of Section 01NS is graded by. It is
`Stacks.TensorPowerPullback.pullbackIntPowIso`. -/
def laurentPullback (g : T' ⟶ T) (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).obj ((laurent L).piece i) ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece i :=
  (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L i).hom

/-- The comparison `g^*(L^{⊗ i}) ⟶ (g^*L)^{⊗ i}` of the integral tensor powers is an
isomorphism. -/
instance isIso_laurentPullback (g : T' ⟶ T)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (i : ℤ) :
    IsIso (laurentPullback g L i) :=
  ⟨(Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L i).inv,
    (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L i).hom_inv_id,
    (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L i).inv_hom_id⟩

/-- **The comparison of the integral tensor powers is multiplicative.** This is
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`, read in the vocabulary of the
Laurent algebra: the comparison carries the coherent multiplication of Tag 01CU for `L` to the
one for `g^*L`, through the comparison of Tag 01CD. -/
theorem laurentPullback_mul (g : T' ⟶ T)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (i j : ℤ) :
    pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i) ((laurent L).piece j) ≫
        (laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
          laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j =
      (pullbackFunctor (ringedSpaceHom g)).map (laurentMul L i j) ≫
        laurentPullback g L (i + j) :=
  have hmap : (tensorSheafMapIso T'.toRingedSpace.presheaf (isSheafStruct T')
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L i)
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom g) L j)).hom =
      (laurentPullback g L i ⊗ₘ laurentPullback g L j) :=
    Stacks.SheafOfModules.tensorSheafMapIso_hom_eq _ _ _ _
  ((Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso (ringedSpaceHom g) L i j).trans
    (congrArg (fun φ => pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i)
        ((laurent L).piece j) ≫ φ ≫
          laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j) hmap)).symm

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The degreewise pullback of the map `ψ` of a quadruple along a morphism `g : T' ⟶ T` of
test schemes**: the component in degree `i` is the contraction of the iterated pullback, followed
by the pullback of `ψ_i`, followed by the comparison `g^*(L^{⊗ i}) ⟶ (g^*L)^{⊗ i}` of the
integral tensor powers of Tag 01CU.

This is the only candidate: a quadruple over `g ≫ f` built from one over `f` has invertible
module `g^*L`, so its map must land in the Laurent algebra of `g^*L`, and the composite above is
the image of `ψ` under the three canonical comparisons available. -/
def pullbackApp (ψ : Twisting f A d L) (g : T' ⟶ T) (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece i :=
  compComparison g f (A.piece (i * d)) ≫
    (pullbackFunctor (ringedSpaceHom g)).map (ψ.app i) ≫ laurentPullback g L i

/-- **Stacks Project, display 01NX, the multiplicativity that makes the pullback of a quadruple
a quadruple.** The pullback of the map `ψ` of a quadruple along a morphism `g : T' ⟶ T` of
test schemes is **multiplicative in every pair of integer degrees**: it carries the
multiplication of `(g ∘ f)^*𝒜^{(d)}` to the multiplication of the Laurent algebra of `g^*L`.
This is exactly the condition `Twisting.app_mul` demands of the map of a quadruple over `g ≫ f`
with invertible module `g^*L`.

The proof is the composite of three compatibilities, each of them available: the multiplicativity
of the comparison of integral tensor powers of Tag 01CU (`laurentPullback_mul`), the naturality
of the comparison of Tag 01CD (`pullbackTensorComparison_naturality_tensorHom`), and the
compatibility of the contraction of an iterated pullback with that comparison
(`compComparison_tensor`) together with its naturality (`compComparison_naturality`). -/
theorem pullbackApp_mul (ψ : Twisting f A d L) (g : T' ⟶ T) (i j : ℤ) :
    (ψ.pullbackApp g i ⊗ₘ ψ.pullbackApp g j) ≫
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) (A.piece (i * d))
            (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          ψ.pullbackApp g (i + j) := by
  have happ := ψ.app_mul i j
  rw [laurent_mulSheaf_eq, IsIso.eq_inv_comp] at happ
  rw [laurent_mulSheaf_eq, IsIso.eq_inv_comp]
  simp only [pullbackApp, ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  slice_lhs 1 2 => rw [← compComparison_tensor g f (A.piece (i * d)) (A.piece (j * d))]
  slice_lhs 3 4 =>
    rw [← pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom g) (ψ.app i) (ψ.app j)]
  slice_lhs 4 6 => rw [laurentPullback_mul g L i j]
  slice_lhs 2 4 =>
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, happ,
      CategoryTheory.Functor.map_comp]
  slice_lhs 1 2 =>
    rw [compComparison_naturality g f (M := A.piece (i * d) ⊗ A.piece (j * d))
      (N := A.piece ((i + j) * d)) (A.mulSheaf (i * d) (j * d) ≫
        eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))]
  simp only [Category.assoc]

/-- **The pullback of `ψ` keeps a surjective homogeneous component surjective.** Section 01NS
requires the degree-one component of the map of a quadruple to be an epimorphism, and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.epi_app_one` records it; the pullback
of sheaves of modules is a left adjoint, hence preserves epimorphisms, and the two comparisons
`compComparison` and `laurentPullback` through which the pullback of `ψ` is built are
isomorphisms. -/
theorem epi_pullbackApp (ψ : Twisting f A d L) (g : T' ⟶ T) (i : ℤ) (hi : Epi (ψ.app i)) :
    Epi (ψ.pullbackApp g i) := by
  have : (pullbackFunctor (ringedSpaceHom g)).IsLeftAdjoint :=
    (pullbackAdjunction (ringedSpaceHom g)).isLeftAdjoint
  have : (pullbackFunctor (ringedSpaceHom g)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  rw [pullbackApp]
  infer_instance

end Twisting

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
