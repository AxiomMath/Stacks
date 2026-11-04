module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.MateStalk
public import StacksFrontier.AlgebraicGeometry.ModuleStalkTensor.Basic

/-!
# The comparison morphism of the quasi-coherence clause of Stacks Tag 01SA, on sections

`Stacks.ModuleStalkTensor.comparison g A` is the morphism of `𝒪_T`-modules
`g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` whose invertibility is the `algebraPullback_isQuasicoherent`
clause of Stacks Tag 01SA, by the reduction
`Stacks.ModuleStalkTensor.isQuasicoherent_of_isIso_comparison`.  It is defined as an adjoint
transpose, so nothing about it is readable off its definition directly.

**This file computes it on sections**, on the only sections that matter for a stalk
computation: those in the image of the unit of the module pullback/pushforward adjunction.  On
`η_V a`, for `a` a section of `A` over an open `V` of `S`, the comparison is
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` applied to the image of `a` under the unit
of the inverse-image/direct-image adjunction on sheaves of commutative rings.

That is the analogue, for the clause of Stacks Tag 01SA, of
`Stacks.PullbackTensorIso.germ_comparison_pullbackUnit` for Stacks Tag 01CD, and it is the
step that the module docstring of
`StacksFrontier/AlgebraicGeometry/ModuleStalkTensor/Basic.lean` calls "the one remaining step
that is not bookkeeping".

## Main results

* `Stacks.AlgebraPullbackQcoh.comparison_app_moduleUnit`: the comparison on the image of the
  unit is `Stacks.ModuleStalkTensor.comparisonPushforward`.  This is the adjunction triangle,
  read on sections.
* `Stacks.AlgebraPullbackQcoh.comparisonPushforward_app`: the sections of
  `comparisonPushforward` are the sections of
  `Stacks.ModuleStalkTensor.adjointAlgebraMap`, on the nose.  Restriction of scalars,
  `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` and
  `CategoryTheory.SheafOfModules.pushforwardCongr` are all the identity on underlying sections.
* `Stacks.AlgebraPullbackQcoh.adjointAlgebraMap_app`: the sections of `adjointAlgebraMap` are
  the inverse-image unit followed by `algebraPullbackMap`.  This is
  `CategoryTheory.Adjunction.homEquiv_unit`, read on sections.
* `Stacks.AlgebraPullbackQcoh.comparison_app_moduleUnit_algebraPullbackMap`: **the three
  composed** — the comparison, on a section in the image of the unit.
* `Stacks.AlgebraPullbackQcoh.germ_comparison_moduleUnit`: the same statement on germs, which is
  the form a stalk computation consumes.

## What is not done

**No clause of [Stacks, Tag 01SA] is proved here, and no project tag attribute is attached.**
The statement of Tag 01SA is a single unqualified tag on a nine-field structure; fields 4, 8 and 9 are
open, and the types of the last two take field 4 as an argument.

The clause is `IsIso (Stacks.ModuleStalkTensor.comparison g A)`.  What this file supplies is
the comparison's effect on germs; what is still missing, after it and after
`StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/MateStalk.lean`, is the identification of
the two sides' stalks as the *same* tensor product and the conclusion that the induced map is
bijective.  Concretely:

* the stalk of the structure sheaf of a scheme, and of an arbitrary sheaf of commutative rings
  on it, taken in `CommRingCat` compared with the stalk taken in `RingCat`.
  `Stacks.PullbackTensorIso.stalkRingIso` and `Stacks.PullbackTensorIso.smul_stalkRingEquiv`
  are exactly this comparison, including the agreement of the two scalar actions, but they are
  stated for the *structure sheaf of a ringed space* in the
    `Stacks.SheafOfModules.TensorStalkRingedSpace` vocabulary, so they
  do not apply verbatim to `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of an algebra
  sheaf on a scheme.  Generalising them in the sheaf argument is what is needed; the technique
  (`CategoryTheory.Limits.preservesColimitIso` for `forget₂ CommRingCat RingCat`) carries over
  unchanged;
* an extension-of-scalars functor at the scheme spelling, left adjoint to restriction of
  scalars along `Stacks.ModuleSkyscraper.stalkRingMap`, whose value is a tensor product over the
  `CommRingCat` stalk — the analogue of `Stacks.PullbackTensorIso.stalkExtendScalarsAdj`,
  likewise stated only for ringed spaces;
* with those, the identification of
  `Stacks.AffineAlgebraEquivalence.stalkAlgebraPullbackIso` and
  `Stacks.ModuleStalkTensor.stalkPullbackModulesIso` as descriptions of the same tensor product
  `A_{g(t)} ⊗_{𝒪_{S,g(t)}} 𝒪_{T,t}`, using
  `Stacks.AlgebraPullbackQcoh.stalkInverseImageMate_inverseImageStructureMap` to see that the
  two base rings act through the same map, and then the germ formula below to see that the
  comparison induces the identity of that tensor product.

None of that is started here.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraPullbackQcoh

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.ModuleStalkTensor

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : AlgebraSheaf S)

/-- **The comparison on the image of the unit is `comparisonPushforward`.**  This is the
triangle identity of the module pullback/pushforward adjunction — `comparison` is the adjoint
transpose of `comparisonPushforward` — read on sections over an open `V` of `S`. -/
public theorem comparison_app_moduleUnit (V : S.Opens)
    (a : (AlgebraSheaf.underlyingModule A).val.obj (op V)) :
    PresheafOfModules.Hom.app (comparison g A).val (op ((Opens.map g.base).obj V))
        (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (AlgebraSheaf.underlyingModule A)).val (op V) a) =
      PresheafOfModules.Hom.app (comparisonPushforward g A).val (op V) a := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
    (AlgebraSheaf.underlyingModule A)
    (AlgebraSheaf.underlyingModule ((algebraPullback g).obj A))).apply_symm_apply
      (comparisonPushforward g A)
  rw [Adjunction.homEquiv_unit] at h
  have h2 : PresheafOfModules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            (AlgebraSheaf.underlyingModule A) ≫
          (Scheme.Modules.pushforward g).map (comparison g A)).val (op V) a =
      PresheafOfModules.Hom.app (comparison g A).val (op ((Opens.map g.base).obj V))
        (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (AlgebraSheaf.underlyingModule A)).val (op V) a) := rfl
  exact h2.symm.trans (congrArg (fun φ => PresheafOfModules.Hom.app φ.val (op V) a) h)

/-- **The sections of `Stacks.ModuleStalkTensor.comparisonPushforward` are the sections of
`Stacks.ModuleStalkTensor.adjointAlgebraMap`.**  On the nose: restriction of scalars does not
change the underlying map on sections,
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of a morphism of sheaves of rings has
that morphism's sections, `CategoryTheory.SheafOfModules.pushforwardCongr` is the identity on
sections, and `forget₂ CommRingCat RingCat` changes neither. -/
public theorem comparisonPushforward_app (V : S.Opens)
    (a : A.right.obj.obj (op V)) :
    PresheafOfModules.Hom.app (comparisonPushforward g A).val (op V) a =
      (adjointAlgebraMap g A).hom.app (op V) a := rfl

/-- **The sections of `Stacks.ModuleStalkTensor.adjointAlgebraMap`.**  It is the adjoint
transpose of `Stacks.AffineAlgebraEquivalence.algebraPullbackMap`, so on sections over `V` it is
the unit of the inverse-image/direct-image adjunction on sheaves of commutative rings followed
by `algebraPullbackMap` over `g⁻¹V`. -/
public theorem adjointAlgebraMap_app (V : S.Opens) (a : A.right.obj.obj (op V)) :
    (adjointAlgebraMap g A).hom.app (op V) a =
      ((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
          A.right).hom.app (op V) a) := by
  have h : adjointAlgebraMap g A =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app A.right) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
          ((algebraPullbackMap g).app A) :=
    Adjunction.homEquiv_unit (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base)
      A.right _ ((algebraPullbackMap g).app A)
  have h2 : ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
            A.right) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
            ((algebraPullbackMap g).app A)).hom.app (op V)) a =
      ((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
          A.right).hom.app (op V) a) := rfl
  exact (congrArg (fun φ => (φ.hom.app (op V)) a) h).trans h2

/-- **The comparison morphism of the quasi-coherence clause of Stacks Tag 01SA, on sections.**
On a section of `g^*A` in the image of the unit of the module pullback/pushforward adjunction,
the comparison is `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` applied to the image of
the section under the unit of the inverse-image/direct-image adjunction on sheaves of
commutative rings. -/
public theorem comparison_app_moduleUnit_algebraPullbackMap (V : S.Opens)
    (a : A.right.obj.obj (op V)) :
    PresheafOfModules.Hom.app (comparison g A).val (op ((Opens.map g.base).obj V))
        (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (AlgebraSheaf.underlyingModule A)).val (op V) a) =
      ((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
          A.right).hom.app (op V) a) :=
  (comparison_app_moduleUnit g A V a).trans
    ((comparisonPushforward_app g A V a).trans (adjointAlgebraMap_app g A V a))

/-- **The comparison morphism of the quasi-coherence clause of Stacks Tag 01SA, on germs.**  The
induced map on the stalk at `t` of the underlying abelian groups carries the germ of the
unit-image of a section `a` of `A` over `V` to the germ of the `algebraPullbackMap`-image of the
inverse-image unit of `a`.

This is `comparison_app_moduleUnit_algebraPullbackMap` read through
`TopCat.Presheaf.stalkFunctor_map_germ_apply`. -/
public theorem germ_comparison_moduleUnit (t : T) (V : S.Opens) (hV : g.base t ∈ V)
    (a : A.right.obj.obj (op V)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
        ((PresheafOfModules.toPresheaf T.ringCatSheaf.obj).map (comparison g A).val)
        (TopCat.Presheaf.germ
          ((Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A)).presheaf
          ((Opens.map g.base).obj V) t hV
          (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            (AlgebraSheaf.underlyingModule A)).val (op V) a)) =
      TopCat.Presheaf.germ
        ((AlgebraSheaf.underlyingModule ((algebraPullback g).obj A)).presheaf)
        ((Opens.map g.base).obj V) t hV
        (((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
            A.right).hom.app (op V) a)) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map g.base).obj V) t hV
      ((PresheafOfModules.toPresheaf T.ringCatSheaf.obj).map (comparison g A).val) _).trans
    (congrArg _ (comparison_app_moduleUnit_algebraPullbackMap g A V a))

end Stacks.AlgebraPullbackQcoh

end

end
