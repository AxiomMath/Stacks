module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of the internal Hom of sheaves of modules

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites and let `F`, `G` be sheaves of
`O_D`-modules. There is a canonical map

`f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)`

of sheaves of `O_C`-modules, and a canonical map

`Hom_{O_D}(F, G) ⟶ f_* Hom_{O_C}(f^*F, f^*G)`

adjoint to it. They are built from the evaluation morphism of the internal Hom sheaf, the
comparison `f^*A ⊗_{O_C} f^*B ≅ f^*(A ⊗_{O_D} B)` of Stacks 03EL, and the
tensor--internal-Hom correspondence of Stacks 03EO.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomEvaluation`: the evaluation morphism
  `Hom_O(F, G) ⊗_O F ⟶ G`.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation`: the morphism `A ⊗_O F ⟶ G` attached to
  a morphism `A ⟶ Hom_O(F, G)`.
* `Stacks.SheafOfModules.InternalHom.ringedSitePullback` and `ringedSitePushforward`: pullback
  and direct image of sheaves of modules along a morphism of ringed sites.
* `Stacks.SheafOfModules.InternalHom.pullbackEvaluation`: the pullback of the evaluation
  morphism, read on the tensor product of the pullbacks.
* `Stacks.SheafOfModules.InternalHom.pullbackInternalHomMap`: the canonical map
  `f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)`.
* `Stacks.SheafOfModules.InternalHom.adjointPullbackInternalHomMap`: its adjoint,
  `Hom_{O_D}(F, G) ⟶ f_* Hom_{O_C}(f^*F, f^*G)`.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_internalHomEvaluation`: evaluation is
  the transpose of the identity of the internal Hom sheaf, which fixes it.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_eq` and `tensorEvaluation_injective`:
  tensoring and evaluating is the inverse of the correspondence of Stacks 03EO, hence
  injective.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_pullbackInternalHomMap`: the canonical map
  is compatible with evaluation — evaluating `Hom_{O_C}(f^*F, f^*G)` after it recovers the
  pulled-back evaluation of `Hom_{O_D}(F, G)`.
  Together with `tensorEvaluation_injective` this determines the canonical map uniquely, so the
  equation pins it down.

## Implementation notes

The two sites, their morphisms and the sections of their structure sheaves lie in one universe.
That is forced by `AlgebraicGeometry.RingedSite.Hom.ringedToposHom`: reading a morphism of
ringed sites as a morphism of ringed topoi needs the exactness of `u_s` on sheaves of sets in
the universe of the site, which is what `CategoryTheory.Functor.IsMorphismOfSites` provides.

Pullback and direct image of sheaves of modules are the ones attached to the associated
morphism of ringed topoi, so that the adjunction of Stacks 03D7 and the tensor comparison of
Stacks 03EL both apply to them. The internal Hom sheaf is the value of the functor of
Stacks 03EN in its second variable, which is the spelling the tensor--internal-Hom
correspondence of Stacks 03EO is stated at; the two tensor products in play, the bifunctor the
comparison of Stacks 03EL is stated with and the curried one that correspondence is stated
with, are the same construction, so nothing is transported between them.

The evaluation morphism is the counit of that correspondence, and the canonical map is the
transpose of the pulled-back evaluation. Both the transpose and the composite of tensoring with
evaluation are named, as `pullbackEvaluation` and `tensorEvaluation`, so that the
characterization below is an identity between two named head symbols rather than a term whose
two sides have to be unified through the correspondence.

What the source displays instead is a description of the adjoint map on sections over an object
`V` of `D`, as pullback along the morphism of localized ringed sites
`(C/u(V), O_{u(V)}) ⟶ (D/V, O_V)` of Stacks 04J0. That description is not proved here.

The two inputs it is usually said to need are both present: the base-change comparison
`f_V^*(F|_V) ≅ (f^*F)|_{u(V)}` of Stacks 04J0 on sheaves of modules is
`AlgebraicGeometry.RingedSite.Hom.localizedPullbackModulesSquare`, and the localization of the
internal Hom sheaf of Stacks 0E8H is
`Stacks.SheafOfModules.ExtensionByZero.internalHomRestrictionNatIso`. So is the input these notes
once recorded as missing: each leg of that localization square is a composite — `f` after a
localization on one side, a localization after `f_V` on the other — so the canonical map above
cannot be moved around the square without the compatibility of the comparison of Stacks 03EL
with *composition* of morphisms of ringed topoi, and that compatibility is proved, at all three
of its levels, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear`:
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp` for the chain of bijections,
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` for the comparison morphism and
`Stacks.SheafOfModules.pullbackTensorIso_inv_app_comp` for the inverse comparison, which is the
direction the canonical map above is built from.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposComp`, which proves the
compatibility for only the first two of the six steps the comparison is built from, is where
that work started and not where it ends.

Carried up to the canonical map itself the law is
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_comp` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompMap`, at
a genuine composite of morphisms of ringed topoi, and
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompData`
with the composite supplied as data, which is the form a square presents; and
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf_congr` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompTwoIso`
equates the two expressions those give for one morphism presented as a composite in two ways,
which is what moving the canonical map around the square amounts to.

What the description on sections still waits on is therefore not the composition law but the
canonical map of a *localization* morphism: the identification of
`pullbackInternalHomMap` at `j_V : (Sh(D/V), O_V) ⟶ (Sh(D), O')` — a morphism of ringed topoi
induced by no morphism of sites — with the localization isomorphism of Stacks 0E8H above. A
formula for the comparison of Stacks 03EL on pure local tensors, which this development does not
have, would be a second route to the same description.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u v

section Evaluation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{max u v}) (F G : SheafOfModules.{max u v} (Tensor.ringSheaf O))

/-- The evaluation morphism `Hom_O(F, G) ⊗_O F ⟶ G` of the internal Hom sheaf of Stacks 03EM:
the counit of the tensor--internal-Hom correspondence of Stacks 03EO. -/
noncomputable def internalHomEvaluation :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj
        ((internalHomSecondFunctor J O F).obj G)).obj F ⟶ G :=
  (sheafTensorRightHomAdjunction O F).counit.app G

/-- Evaluation is the transpose of the identity: it is the morphism out of
`Hom_O(F, G) ⊗_O F` that the correspondence of Stacks 03EO carries to the identity of the
internal Hom sheaf. -/
theorem sheafTensorHomEquiv_internalHomEvaluation :
    sheafTensorHomEquiv O ((internalHomSecondFunctor J O F).obj G) F G
        (internalHomEvaluation O F G) =
      𝟙 ((internalHomSecondFunctor J O F).obj G) :=
  ((sheafTensorRightHomAdjunction O F).homEquiv_unit
      ((internalHomSecondFunctor J O F).obj G) G (internalHomEvaluation O F G)).trans
    ((sheafTensorRightHomAdjunction O F).right_triangle_components G)

variable {A : SheafOfModules.{max u v} (Tensor.ringSheaf O)}

/-- The morphism `A ⊗_O F ⟶ G` attached to a morphism `A ⟶ Hom_O(F, G)`: tensor it with `F`,
then evaluate. -/
noncomputable def tensorEvaluation (φ : A ⟶ (internalHomSecondFunctor J O F).obj G) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj F ⟶ G :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor O).map φ).app F ≫ internalHomEvaluation O F G

/-- Tensoring with `F` and evaluating is the inverse of the correspondence of Stacks 03EO. -/
theorem tensorEvaluation_eq (φ : A ⟶ (internalHomSecondFunctor J O F).obj G) :
    tensorEvaluation O F G φ = (sheafTensorHomEquiv O A F G).symm φ :=
  ((sheafTensorRightHomAdjunction O F).homEquiv_counit A G φ).symm

/-- A morphism `A ⟶ Hom_O(F, G)` is determined by the morphism `A ⊗_O F ⟶ G` it induces. -/
theorem tensorEvaluation_injective :
    Function.Injective (tensorEvaluation O F G (A := A)) := fun a b h ↦
  (sheafTensorHomEquiv O A F G).symm.injective
    ((tensorEvaluation_eq O F G a).symm.trans (h.trans (tensorEvaluation_eq O F G b)))

end Evaluation

section Pullback

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The pullback of sheaves of modules along a morphism of ringed sites
`f : (C, O_C) ⟶ (D, O_D)`: the pullback `f^* : Mod(O_D) ⥤ Mod(O_C)` of Stacks 03D6 along the
morphism of ringed topoi that `f` defines. -/
noncomputable abbrev ringedSitePullback :
    SheafOfModules.{u} (Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Tensor.ringSheaf X.O) :=
  f.ringedToposHom.toModulesHom.pullbackModules

/-- The direct image of sheaves of modules along a morphism of ringed sites
`f : (C, O_C) ⟶ (D, O_D)`: the direct image `f_* : Mod(O_C) ⥤ Mod(O_D)` of Stacks 03D6 along
the morphism of ringed topoi that `f` defines. -/
noncomputable abbrev ringedSitePushforward :
    SheafOfModules.{u} (Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Tensor.ringSheaf Y.O) :=
  RingedToposHom.pushforwardModules (X := RingedSite.ringedTopos X)
    (Y := RingedSite.ringedTopos Y) f.ringedToposHom

variable (F G : SheafOfModules.{u} (Tensor.ringSheaf Y.O))

/-- The pullback of the evaluation morphism of `Hom_{O_D}(F, G)`, read as a morphism out of
`f^* Hom_{O_D}(F, G) ⊗_{O_C} f^*F` through the tensor comparison of Stacks 03EL. -/
noncomputable def pullbackEvaluation :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((ringedSitePullback f).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))).obj
        ((ringedSitePullback f).obj F) ⟶
      (ringedSitePullback f).obj G :=
  (Stacks.SheafOfModules.pullbackTensorIso f.ringedToposHom.toModulesHom).inv.app
      ((internalHomSecondFunctor Y.J Y.O F).obj G, F) ≫
    (ringedSitePullback f).map (internalHomEvaluation Y.O F G)

/-- **Stacks 0GMX.** The canonical map `f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)` attached
to a morphism of ringed sites: the transpose, under the correspondence of Stacks 03EO, of the
pullback of the evaluation morphism. -/
@[stacks 0GMX "the canonical map"]
noncomputable def pullbackInternalHomMap :
    (ringedSitePullback f).obj ((internalHomSecondFunctor Y.J Y.O F).obj G) ⟶
      (internalHomSecondFunctor X.J X.O ((ringedSitePullback f).obj F)).obj
        ((ringedSitePullback f).obj G) :=
  sheafTensorHomEquiv X.O
    ((ringedSitePullback f).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
    ((ringedSitePullback f).obj F) ((ringedSitePullback f).obj G) (pullbackEvaluation f F G)

/-- **Stacks 0GMX.** The map `Hom_{O_D}(F, G) ⟶ f_* Hom_{O_C}(f^*F, f^*G)` displayed in the
source: the adjoint of `pullbackInternalHomMap` under the adjunction `f^* ⊣ f_*` of
Stacks 03D7. -/
@[stacks 0GMX "the adjoint map"]
noncomputable def adjointPullbackInternalHomMap :
    (internalHomSecondFunctor Y.J Y.O F).obj G ⟶
      (ringedSitePushforward f).obj
        ((internalHomSecondFunctor X.J X.O ((ringedSitePullback f).obj F)).obj
          ((ringedSitePullback f).obj G)) :=
  (RingedToposHom.pullbackAdjPushforwardModules f.ringedToposHom).homEquiv _ _
    (pullbackInternalHomMap f F G)

/-- **Stacks 0GMX.** The canonical map is compatible with evaluation: tensoring it with `f^*F`
and then evaluating `Hom_{O_C}(f^*F, f^*G)` gives the pulled-back evaluation of
`Hom_{O_D}(F, G)`. -/
@[stacks 0GMX "compatibility of the canonical map with evaluation"]
theorem tensorEvaluation_pullbackInternalHomMap :
    tensorEvaluation X.O ((ringedSitePullback f).obj F) ((ringedSitePullback f).obj G)
        (pullbackInternalHomMap f F G) =
      pullbackEvaluation f F G :=
  (tensorEvaluation_eq X.O ((ringedSitePullback f).obj F) ((ringedSitePullback f).obj G)
      (pullbackInternalHomMap f F G)).trans
    ((sheafTensorHomEquiv X.O
        ((ringedSitePullback f).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
        ((ringedSitePullback f).obj F)
        ((ringedSitePullback f).obj G)).symm_apply_apply (pullbackEvaluation f F G))

end Pullback

end Stacks.SheafOfModules.InternalHom

end
