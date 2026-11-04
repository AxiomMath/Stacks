module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerNaturality

/-!
# Pulling an integer invertible ideal power back along a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `I` be an invertible sheaf of
`𝒪_Y`-modules. The degree-`n` term of the sheaf-theoretic décalage of Tag 0GT6 is built from the
integer ideal power `I^{⊗ n} ⊗ -` of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf`, so
comparing a décalage on `Y` with a décalage on `X` requires first knowing that `f^*` carries that
power to the corresponding power of `f^*I`. This file proves exactly that, in every integer
degree, naturally in the module:

`f^*(I^{⊗ n} ⊗ M) ≅ (f^*I)^{⊗ n} ⊗ f^*M`.

Nothing about the décalage itself is used or claimed here: this is the interchange of a pullback
with an integer ideal power, and it is the first of the two inputs that a comparison of décalages
needs (the second being that `f^*` carries the fibre product defining the décalage term to the
corresponding fibre product, which is **not** proved here).

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackIdealPowerIso`: **the interchange
  `f^*(I^{⊗ n} ⊗ M) ≅ (f^*I)^{⊗ n} ⊗ f^*M`,** for every `n : ℤ`.

## Main results

* `Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal`: the pullback of an invertible sheaf of
  modules is invertible, restated at the spelling of the structure sheaf that `EtaSheaf.lean`
  uses, so that `idealPowerTerm` can be formed for `f^*I`. This is Tag 0B8L, retyped; the
  mathematics is `Stacks.RingedSpace.modulePullback_isInvertible`.
* `Stacks.IdealTorsion.Eta.pullbackIdealPowerIso_zero` and `pullbackIdealPowerIso_one`: **the
  normalisation.** In degree `0` the interchange is the identity, and in degree `1` it is the
  canonical comparison of Tag 01CD, `Stacks.RingedSpace.comparisonBifunctorIso`. Both hold by
  `rfl`, so the interchange is pinned to the canonical comparison with no choice intervening.
* `Stacks.IdealTorsion.Eta.pullbackIdealPowerIso_natural`: **the interchange is natural in the
  module** in every integer degree.

## Implementation notes

**Where the content comes from, and what is new.** Both ingredients already existed and neither
is rebuilt. The degree-`1` case is `Stacks.RingedSpace.comparisonBifunctorIso`, the Tag 01CD
isomorphism of bifunctors `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso`, which is already
identified with the canonical comparison morphism. The passage from degree `1` to every integer
degree is `Stacks.Equivalence.powIntertwineObj` of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner`, which transports a comparison between
two autoequivalences across a functor to all their integer iterates; `idealPowerTerm` is by
definition such an iterate, since `Stacks.SheafOfModules.Invertible.tensorPowerEquivalence` is
`(- ⊗ I).asEquivalence ^ n`. What this file adds is the observation that the two fit together on
the nose — the degree-`1` comparison of Tag 01CD *is* an `α` for that transport, with no
conversion at all, which is why `pullbackIdealPowerIso_one` is `rfl` — together with the
naturality, which `powIntertwineObj` does not provide and which
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerNaturality` supplies from naturality of the
degree-`1` comparison.

**The two spellings of the structure sheaf.** `EtaSheaf.lean` indexes its sheaves of modules by
`structureSheaf X.sheaf`, while the Tag 01CD development indexes them by
`Stacks.RingedSpace.structureRingSheaf X`. The two are the same sheaf of rings — compare
`Stacks.SheafOfModules.TensorEncodings.ringSheaf_eq_structureSheaf` — and the equality is by
`rfl`, so every statement below is written once, at the `EtaSheaf.lean` spelling, and the
definitional check of `:=` crosses the boundary. What does *not* cross is instance search: the
recorded form of Tag 0B8L is stated at the `X.presheaf` spelling and its discrimination-tree key
does not match a goal written with `X.sheaf.obj`, which is why `isInvertible_pullbackIdeal`
exists and supplies the hypothesis by ascription rather than by `inferInstance`.

For the same reason `isEquivalence_tensorRightFunctorObj` is a `private` instance here. It is
definitionally `Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`, restated at
the `EtaSheaf.lean` spelling so that the two `asEquivalence` in `pullbackIdealPowerIso` — one on
`Y` and one on `X`, the latter at the pulled-back ideal — are found without unfolding. This is the
same discipline as the `private instance isEquivalence_tensorRightFunctor` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafTensor`, and no limit is raised anywhere.

**What is not here.** No tag is attached. Tag 0F9X asserts an equality
`Lf^*(Lη_I M) = Lη_J(Lf^* M)` in the derived category, and the named comparison map it needs
requires, beyond the interchange proved here, that `f^*` carry the fibre product of
`Stacks.IdealTorsion.Eta.etaTerm` to the fibre product of the pulled-back data. That is a
statement about `f^*` preserving a limit, which a left adjoint does not do in general; it is true
under flatness of `f`, and it is not proved here. Until it is, the degreewise comparison of
décalages cannot be written down, so neither can the map of Tag 0F9X.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
-/

@[expose] public section

/- The spelling `structureSheaf X.sheaf` of the structure sheaf of rings is a composite of
definitions that are not reducible, so instance search does not see through it and the
`IsEquivalence` instances for `tensorRightFunctor` are not found at goals written this way.
Making the links locally unfoldable is what lets them be found; this is the same declaration,
for the same reason, as in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafTensor`. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence)

open Stacks.RingedSpace (pullbackFunctor comparisonBifunctorIso)

universe u

namespace Stacks.IdealTorsion.Eta

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- Tensoring on the right by an invertible module is an equivalence, restated at the spelling
of the structure sheaf used by `EtaSheaf.lean` so that instance search finds it without
unfolding. -/
private noncomputable instance isEquivalence_tensorRightFunctorObj (Z : RingedSpace.{u})
    (L : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Z.sheaf).flip.obj L).IsEquivalence :=
  tensorRightFunctor_isEquivalence Z.sheaf.obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)).property L

/-- **Stacks Project, Tag 0B8L**, at the structure-sheaf spelling of `EtaSheaf.lean`: the
pullback of an invertible sheaf of modules along a morphism of ringed spaces is invertible. The
mathematics is `Stacks.RingedSpace.modulePullback_isInvertible`; only the spelling of the
structure sheaf, and hence the shape instance search sees, is different. -/
public instance isInvertible_pullbackIdeal
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [h : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property ((pullbackFunctor f).obj I) :=
  letI : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ Y.presheaf (forget₂ CommRingCat RingCat) Y.IsSheaf) I :=
    h
  Stacks.RingedSpace.modulePullback_isInvertible f I

/-- **The interchange of a pullback with an integer invertible ideal power**,
`f^*(I^{⊗ n} ⊗ M) ≅ (f^*I)^{⊗ n} ⊗ f^*M`. The degree-`1` comparison is the canonical one of
Tag 01CD and the passage to every integer degree is the transport of that comparison along the
iterates of the two tensor autoequivalences. -/
public noncomputable def pullbackIdealPowerIso
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (n : ℤ) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    (pullbackFunctor f).obj (idealPowerTerm Y I n M) ≅
      idealPowerTerm X ((pullbackFunctor f).obj I) n ((pullbackFunctor f).obj M) :=
  Stacks.Equivalence.powIntertwineObj
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Y.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence Y.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj
        ((pullbackFunctor f).obj I))
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property ((pullbackFunctor f).obj I)))
    (pullbackFunctor f)
    (fun N => (comparisonBifunctorIso f).app (N, I)) n M

/-- In degree `0` the interchange is the identity: the zeroth ideal power is the module itself. -/
public theorem pullbackIdealPowerIso_zero
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    pullbackIdealPowerIso f I 0 M = Iso.refl ((pullbackFunctor f).obj M) :=
  rfl

/-- **The normalisation of the interchange.** In degree `1` it is the canonical comparison
morphism of Stacks 01CD, so the interchange involves no choice beyond that comparison. -/
public theorem pullbackIdealPowerIso_one
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    pullbackIdealPowerIso f I 1 M = (comparisonBifunctorIso f).app (M, I) :=
  rfl

/-- **The interchange is natural in the module**, in every integer degree. -/
public theorem pullbackIdealPowerIso_natural
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (n : ℤ) {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))}
    (a : M ⟶ N) :
    (pullbackFunctor f).map (idealPowerMap Y I n a) ≫ (pullbackIdealPowerIso f I n N).hom =
      (pullbackIdealPowerIso f I n M).hom ≫
        idealPowerMap X ((pullbackFunctor f).obj I) n ((pullbackFunctor f).map a) := by
  refine Stacks.Equivalence.powIntertwineObj_naturality
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Y.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence Y.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj
        ((pullbackFunctor f).obj I))
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property ((pullbackFunctor f).obj I)))
    (pullbackFunctor f)
    (fun P => (comparisonBifunctorIso f).app (P, I)) (fun {P Q} b => ?_) n a
  -- Naturality of the Tag 01CD comparison in its first variable, which is its naturality as a
  -- transformation of bifunctors at the morphism `(b, 𝟙 I)` of the product category. The
  -- `Functor.map_id` step is the only gap: the target of that square carries `f^*(𝟙 I)` where
  -- tensoring on the right by `f^*I` carries `𝟙 (f^*I)`, and the two agree propositionally.
  have h := (comparisonBifunctorIso f).hom.naturality (X := (P, I)) (Y := (Q, I)) (b, 𝟙 I)
  let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Y.sheaf
  let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf
  let pullback := pullbackFunctor f
  have sourceIdentity : (Functor.uncurry.obj sourceTensor).map
      (X := (P, I)) (Y := (Q, I)) (b, 𝟙 I) = (sourceTensor.map b).app I :=
    (congrArg (fun morphism => (sourceTensor.map b).app I ≫ morphism)
      ((sourceTensor.obj Q).map_id I)).trans (Category.comp_id _)
  have targetIdentity : (Functor.uncurry.obj targetTensor).map
      (X := (pullback.obj P, pullback.obj I)) (Y := (pullback.obj Q, pullback.obj I))
      (pullback.map b, pullback.map (𝟙 I)) =
        (targetTensor.map (pullback.map b)).app (pullback.obj I) :=
    (congrArg (fun morphism => (Functor.uncurry.obj targetTensor).map
      (X := (pullback.obj P, pullback.obj I)) (Y := (pullback.obj Q, pullback.obj I))
      (pullback.map b, morphism)) (pullback.map_id I)).trans
        ((congrArg (fun morphism =>
          (targetTensor.map (pullback.map b)).app (pullback.obj I) ≫ morphism)
          ((targetTensor.obj (pullback.obj Q)).map_id (pullback.obj I))).trans
            (Category.comp_id _))
  exact (congrArg (fun morphism =>
    pullback.map morphism ≫ (comparisonBifunctorIso f).hom.app (Q, I)) sourceIdentity.symm).trans
      (h.trans (congrArg (fun morphism =>
        (comparisonBifunctorIso f).hom.app (P, I) ≫ morphism) targetIdentity))

end Stacks.IdealTorsion.Eta

end
