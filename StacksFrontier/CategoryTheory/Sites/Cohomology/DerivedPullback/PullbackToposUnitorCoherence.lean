module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The module-level comparison behind the comparison of total tensor complexes

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites, and let `f^*` be the pullback of sheaves of
modules attached to that presentation (`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`). The
comparison of total tensor complexes

`f^*Tot(K ⊗_{𝒪_D} L) ≅ Tot(f^*K ⊗_{𝒪_C} f^*L)`

of `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` is assembled from three
isomorphisms. This file extracts the **module-level** comparison

`f^*(A ⊗_{𝒪_D} B) ≅ f^*A ⊗_{𝒪_C} f^*B`

out of which it is built — the comparison of **Stacks 03EL** for the four-field pullback of
Stacks 03D6, transported along the identification of the two pullbacks — and proves that the
comparison of total complexes acts on the summand of bidegree `(p, q)` by it, as
`Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom` does for the four-field pullback.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom`: the comparison of Stacks 03EL
  `f^*(F ⊗_{𝒪_D} G) ⟶ f^*F ⊗_{𝒪_C} f^*G` for a morphism of ringed topoi, with its source and
  target ascribed so that it can be composed; see the implementation notes.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap`: the comparison
  `f^*(A ⊗_{𝒪_D} B) ⟶ f^*A ⊗_{𝒪_C} f^*B` for the site-presented pullback. It is a composite of
  four isomorphisms, so it is invertible; no `IsIso` instance is registered here, because
  instance search does not see through the three spellings of the structure sheaf of the source
  that the composite crosses.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg`: the same comparison at the modules
  `K^p` and `L^q` of two complexes, with its target spelled at the degrees of the pullback
  complexes; see the implementation notes.
* `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`: the module-level
  right-unitor coherence, written out as a proposition. It is proved by
  `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposRightUnitorCoherence`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp`: **the universal property of
  the comparison of Stacks 03EL, as a composition formula.** For every `N` and every
  `k : f^*F ⊗_{𝒪_C} f^*G ⟶ N`, the comparison followed by `k` is the preimage of `k` under the
  chain of bijections of Stacks 03EL.  The chain being injective, this turns any identity whose
  left-hand side begins with the comparison into an identity of morphisms out of
  `f^*F ⊗_{𝒪_C} f^*G`, with the comparison eliminated.
  `pullbackTensorHomEquiv_pullbackTensorComparisonHom` is the
  underlying fact that the chain carries the comparison to the identity, restated so that both
  sides are spelled one way.
* `Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom`: **the comparison of total
  tensor complexes for the site-presented pullback acts on the summand of bidegree `(p, q)` by
  the module-level comparison.**
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg_eq`: the degreewise comparison is
  the module-level one at the modules of that bidegree.

## Implementation notes

**Three spellings of the structure sheaf of the source, and what they cost.** The composite that
the summandwise formula is about crosses three spellings of the sheaf of rings over which the
sheaves of `𝒪_C`-modules are taken: `AlgebraicGeometry.RingedTopos.ringSheaf X`, which is the
codomain of `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`;
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`, over which
`Stacks.Sheaves.RingedToposModules.pullbackModules` and the comparison of Stacks 03EL are
stated; and `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, over which the tensor bifunctor of
Tag 06YM and the whole derived development are stated. All three are
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.O` with a different `HasSheafCompose`
instance named, so they are equal by proof irrelevance; but they are not syntactically equal, and
that has two consequences, both of which shape this file.

*`rw` and `simp` stop working across a seam carrying two spellings.* A composite `(a ≫ b) ≫ c`
in which `b`'s target and `c`'s source are two spellings of the same object is a term in which
`rw [Category.assoc]` reports that it cannot find the pattern `(?f ≫ ?g) ≫ ?h`: matching it
means deciding the equality of the two spellings of the seam, and deciding that means unfolding
the sheaf tensor product. The two cures used here are to restate an imported lemma once in the
spelling of the goal — `ι_pullbackTensorTotalIso_hom'` — and to supply the reassociations in term
position with every argument written out, through the generic `comp_comp_of_comp_eq`, where
associativity is applied at objects that are variables.

*The kernel has a budget too.* Composing `pullbackToposTensorMap f hmos (K.X p) (L.X q)`, whose
target is `(f^*(K^p)) ⊗ (f^*(L^q))`, directly with the summand inclusion of the total complex of
the pullbacks, whose source is `((f^*K)^p) ⊗ ((f^*L)^q)`, produces an equation the *kernel*
cannot check inside its step limit — the elaborator accepts it and the declaration is then
rejected after the proof is complete. `pullbackToposTensorMapDeg` is the composite declared once
at the second spelling, which absorbs the definitional equality into a declared type.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

private lemma naturality_comp_comparison
    {Source Target : Type*} [Category Source] [Category Target]
    {firstFunctor secondFunctor : Source ⥤ Target}
    (change : firstFunctor ⟶ secondFunctor) {source target : Source}
    {middle firstFactor secondFactor thirdFactor last : Target}
    (inclusion : source ⟶ target)
    (comparison : secondFunctor.obj target ⟶ middle) (factorMap : middle ⟶ last)
    (moduleComparison : secondFunctor.obj source ⟶ firstFactor)
    (leftMap : firstFactor ⟶ secondFactor) (rightMap : secondFactor ⟶ thirdFactor)
    (targetInclusion : thirdFactor ⟶ last)
    (compatibility : secondFunctor.map inclusion ≫ comparison ≫ factorMap =
      moduleComparison ≫ leftMap ≫ rightMap ≫ targetInclusion) :
    firstFunctor.map inclusion ≫ change.app target ≫ comparison ≫ factorMap =
      (change.app source ≫ moduleComparison ≫ leftMap ≫ rightMap) ≫ targetInclusion :=
  by rw [change.naturality_assoc, compatibility]; simp only [Category.assoc]

/-- Appending a morphism to a two-fold composite whose value is already known, in an arbitrary
category: `second` is evaluated by `hFirst`, the appended morphism is rewritten by `hAppended`,
and `hValue` evaluates what the appended morphism does to the result.

Stated generically so that the objects are variables, for a sharp reason. At the objects of the
summandwise formula below every morphism is spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is a semireducible `def`; reassociating in place
makes the unifier try to see through it below default transparency and the elaborator's budget
is exhausted before the three associativity steps are done. Here the objects are variables, so
there is nothing to unfold, and the real goal is reached by one application. -/
private lemma comp_comp_of_comp_eq {C : Type*} [Category C] {A B D E G : C}
    {first : A ⟶ B} {second : B ⟶ D} {appended rewritten : D ⟶ G}
    {comparison : A ⟶ E} {inclusion : E ⟶ D} {value : E ⟶ G}
    (hAppended : appended = rewritten)
    (hFirst : first ≫ second = comparison ≫ inclusion)
    (hValue : inclusion ≫ rewritten = value) :
    first ≫ second ≫ appended = comparison ≫ value := by
  rw [hAppended, ← Category.assoc, hFirst, Category.assoc, hValue]

/-! ## The universal property of the comparison of Stacks 03EL -/

section Comparison

universe v₂ u₂ w₂ v₃ u₃ w₃

variable {X : RingedTopos.{v₂, u₂, w₂}} {Y : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget RingCat.{w₂})] [Y.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X.J AddCommGrpCat.{w₂}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₃}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w₃} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The comparison `f^*(F ⊗_{𝒪_D} G) ⟶ f^*F ⊗_{𝒪_C} f^*G` of Stacks 03EL, with its source and
target ascribed**, namely as the preimage of the identity under the chain of bijections
`Stacks.SheafOfModules.pullbackTensorHomEquiv`.

This is `(Stacks.SheafOfModules.pullbackTensorIso g).hom.app (F, G)` — see
`pullbackTensorComparisonHom_eq` — and the ascription is the only difference. It is forced rather
than chosen: the target of `Iso.hom.app` is obtained by composing the product of the
pullback functors with `Functor.uncurry.obj (sheafTensor X.O)`, while the expressions composed
with it use the native object `((sheafTensor X.O).obj _).obj _`. These
are definitionally equal only at *default* transparency, so a goal carrying both is not
type-correct at `implicit` transparency; `Equiv.apply_symm_apply` applied to the second form in a
goal written in the first does not merely fail to rewrite, it exhausts the unifier's recursion
budget.  Declaring the morphism once at the second spelling absorbs that definitional equality
into a declared type. -/
def pullbackTensorComparisonHom :
    (g.pullbackModules).obj
        (((sheafTensor.{u₃, v₃, w₃, w₃, w₃} Y.O).obj F).obj G) ⟶
      ((sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G) :=
  (Stacks.SheafOfModules.pullbackTensorHomEquiv g F G
      (((sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G))).symm
    (𝟙 (((sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G)))

/-- The ascribed comparison is the comparison of Stacks 03EL, by
`Stacks.SheafOfModules.pullbackTensorIso_hom_app`. -/
lemma pullbackTensorComparisonHom_eq :
    pullbackTensorComparisonHom g F G =
      (Stacks.SheafOfModules.pullbackTensorIso g).hom.app (F, G) := rfl

/-- **The chain of bijections of Stacks 03EL carries the comparison to the identity.**  This is
`Stacks.SheafOfModules.pullbackTensorIso_hom_app` with both sides of the chain spelled the same
way, which is what makes it usable by `rw`. -/
lemma pullbackTensorHomEquiv_pullbackTensorComparisonHom :
    Stacks.SheafOfModules.pullbackTensorHomEquiv g F G
        (((sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G))
      (pullbackTensorComparisonHom g F G) = 𝟙 _ :=
  Equiv.apply_symm_apply _ _

/-- **The universal property of the comparison of Stacks 03EL, as a composition formula:** for
every sheaf of `𝒪_C`-modules `N` and every `k : f^*F ⊗_{𝒪_C} f^*G ⟶ N`, the comparison followed
by `k` is the preimage of `k` under the chain of bijections of Stacks 03EL.

`Stacks.SheafOfModules.pullbackTensorIso` is produced by
`CategoryTheory.Functor.natIsoOfHomEquiv` out of `Stacks.SheafOfModules.pullbackTensorHomEquiv`,
which characterises it as the morphism the chain carries to the identity. This formula says that
*every* morphism out of `f^*(F ⊗ G)` which factors through the comparison is determined by its
second factor: the chain of bijections being injective, an identity whose left-hand side is a
composite starting with the comparison is equivalent to an identity of morphisms
`f^*F ⊗_{𝒪_C} f^*G ⟶ N`, with the comparison eliminated. -/
lemma pullbackTensorComparisonHom_comp
    {N : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : ((sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G) ⟶ N) :
    pullbackTensorComparisonHom g F G ≫ k =
      (Stacks.SheafOfModules.pullbackTensorHomEquiv g F G N).symm k := by
  apply (Stacks.SheafOfModules.pullbackTensorHomEquiv g F G N).injective
  exact ((Stacks.SheafOfModules.pullbackTensorHomEquiv_naturality g F G
    (pullbackTensorComparisonHom g F G) k).trans
      ((congrArg (fun morphism => morphism ≫ k)
        (pullbackTensorHomEquiv_pullbackTensorComparisonHom g F G)).trans
          (Category.id_comp k))).trans
    ((Stacks.SheafOfModules.pullbackTensorHomEquiv g F G N).apply_symm_apply k).symm

/-! ### The comparison moved to the target topos -/

/-- **The adjoint transpose of the comparison of Stacks 03EL**: the image of
`pullbackTensorComparisonHom` under the adjunction of Stacks 03D7, a morphism

`F ⊗_{𝒪_D} G ⟶ f_*(f^*F ⊗_{𝒪_C} f^*G)`

of sheaves of `𝒪_D`-modules.

The adjunction being a bijection, this carries the whole content of the comparison, and it
carries it to the *target* topos — where the source of the morphism is a tensor product sheaf of
two sheaves on `D` and therefore has local sections, which is what
`pullbackTensorComparisonHom_comp_eq_iff` exploits. -/
def pullbackTensorAdjTranspose :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₃, v₃, w₃, w₃, w₃} Y.O).obj F).obj G) ⟶
      (pushforwardModules g).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
          ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G))) :=
  (pullbackAdjPushforwardModules g).homEquiv _ _ (pullbackTensorComparisonHom g F G)

/-- **Step 1 of the chain of Stacks 03EL cancels in the adjoint transpose of the comparison.**
The adjoint transpose is the preimage of the identity under the *last five* steps of the chain:
the comparison is the preimage of the identity under all six, step 1 is the adjunction, and
transposing undoes it.

Consequently the identity that `pullbackTensorComparisonHom_comp_eq_iff` produces on the target
topos is about a morphism out of `F ⊗_{𝒪_D} G` whose only remaining content is steps 2 to 6, and
its pairing on a pair of local sections is computed by traversing those five. -/
lemma pullbackTensorAdjTranspose_eq :
    pullbackTensorAdjTranspose g F G =
      (Stacks.SheafOfModules.pullbackTensorStep2 g F G _).symm
        ((Stacks.SheafOfModules.pullbackTensorStep3 g F G _).symm
          ((Stacks.SheafOfModules.pullbackTensorStep4 g F G _).symm
            ((Stacks.SheafOfModules.pullbackTensorStep5 g F G _).symm
              ((Stacks.SheafOfModules.pullbackTensorStep6 g F G
                  ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
                    ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G)))).symm
                (𝟙 _))))) :=
  Equiv.apply_symm_apply (Stacks.SheafOfModules.pullbackTensorStep1 g F G _) _

/-- The image of the comparison of Stacks 03EL under the hom-set bijection of the adjunction is
`pullbackTensorAdjTranspose`; recorded so that a goal written with the `Equiv` can rewrite to the
name. -/
lemma homEquiv_pullbackTensorComparisonHom :
    (pullbackAdjPushforwardModules g).homEquiv _ _ (pullbackTensorComparisonHom g F G) =
      pullbackTensorAdjTranspose g F G := rfl

/-- The adjoint transpose of a composite beginning with the comparison of Stacks 03EL is the
adjoint transpose of the comparison, followed by the direct image of the second factor. This is
the naturality of the adjunction of Stacks 03D7 in the sheaf of values, read at the comparison. -/
lemma homEquiv_pullbackTensorComparisonHom_comp
    {N : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
      ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G)) ⟶ N) :
    (pullbackAdjPushforwardModules g).homEquiv _ N
        (pullbackTensorComparisonHom g F G ≫ k) =
      pullbackTensorAdjTranspose g F G ≫ (pushforwardModules g).map k :=
  (pullbackAdjPushforwardModules g).homEquiv_naturality_right _ _

/-- **Any identity whose left-hand side begins with the comparison of Stacks 03EL is an identity
of morphisms out of `F ⊗_{𝒪_D} G`, with the comparison replaced by its adjoint transpose.**

This is the sharpening of `pullbackTensorComparisonHom_comp` that moves the problem to the target
topos. That lemma rewrites such an identity to one in `Hom_{𝒪_C}(f^*F ⊗_{𝒪_C} f^*G, N)` — still on
the source topos, where the tensor factors are pullbacks and have no local sections, so the chain
of Stacks 03EL still has to be evaluated step by step. The present form rewrites it instead to one
in `Hom_{𝒪_D}(F ⊗_{𝒪_D} G, f_*N)`, whose source is the tensor product sheaf of two sheaves on `D`;
two morphisms out of it agree as soon as the pairings they induce agree on pairs of local
sections, by `Stacks.SheafOfModules.pairingApp_bilinearEquivTensorSheafHom_symm` and
`Stacks.SheafOfModules.pairing_ext`. Such an identity therefore reduces to a single value formula
— the local sections of `pullbackTensorAdjTranspose` — rather than one formula per step. -/
lemma pullbackTensorComparisonHom_comp_eq_iff
    {N : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w₂, w₂, w₂} X.O).obj
      ((g.pullbackModules).obj F)).obj ((g.pullbackModules).obj G)) ⟶ N)
    (m : (g.pullbackModules).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u₃, v₃, w₃, w₃, w₃} Y.O).obj F).obj G)) ⟶
        N) :
    pullbackTensorComparisonHom g F G ≫ k = m ↔
      pullbackTensorAdjTranspose g F G ≫ (pushforwardModules g).map k =
        (pullbackAdjPushforwardModules g).homEquiv _ N m := by
  rw [← homEquiv_pullbackTensorComparisonHom_comp]
  exact (((pullbackAdjPushforwardModules g).homEquiv _ N).apply_eq_iff_eq).symm

end Comparison

/-! ## A section formula for the unit comparison -/

section UnitComparison

universe u₄

variable {X Y : RingedTopos.{u₄, u₄, u₄}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u₄} RingCat.{u₄})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u₄} RingCat.{u₄})]
  [HasSheafify X.J AddCommGrpCat.{u₄}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u₄}]
  (f : RingedToposSiteHom X Y)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u₄} RingCat.{u₄})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u₄} RingCat.{u₄})]
  [HasSheafify X.J AddCommGrpCat.{u₄}] in
/-- **The pullback of a function is the function pulled back.** The unit comparison
`ν : f^*𝒪_D ⟶ 𝒪_C` of `SheafOfModules.pullbackObjUnitToUnit` carries the image of a local section
`r` of `𝒪_D` under the unit of `f^* ⊣ f_*` to `f^♯ r`.

This is the ringed-topos analogue of
`Stacks.RingedSpaceModuleAdjunction.pullbackObjUnitToUnit_val_app_unit`. There is nothing in it
beyond the adjunction: `SheafOfModules.pullbackObjUnitToUnit` is by definition the adjoint
transpose of `SheafOfModules.unitToPushforwardObjUnit`, whose value on a local section is `f^♯`
by Mathlib's `SheafOfModules.unitToPushforwardObjUnit_val_app_apply`, so the unit form of the
hom-set bijection is the whole proof. -/
theorem pullbackObjUnitToUnit_val_app_unit (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    (_root_.SheafOfModules.pullbackObjUnitToUnit.{u₄} f.fSharpRing).val.app (f.u.op.obj U)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u₄} f.fSharpRing).unit.app
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val.app U r) =
      f.fSharpRing.hom.app U r := by
  have h := (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u₄} f.fSharpRing).homEquiv_unit
    (f := _root_.SheafOfModules.pullbackObjUnitToUnit.{u₄} f.fSharpRing)
  rw [_root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit] at h
  exact (congrArg (fun m ↦ m.val.app U r) h).symm

end UnitComparison

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-! ## Two restatements, in the spelling of the derived development -/

/-- `Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom`, restated with its complexes
typed over `Stacks.SheafOfModules.Tensor.ringSheaf Y.O` rather than over
`Stacks.SheafOfModules.Tensor.ringSheaf Y.O`.

The two sheaves of rings differ only in which `HasSheafCompose` instance they name, so they are
equal by proof irrelevance and this is the same theorem; but the two spellings are not
syntactically equal, so `rw` refuses to use the imported form inside a goal written in the
second. Restating once absorbs the definitional equality into a declared type. -/
private lemma ι_pullbackTensorTotalIso_hom'
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (g.pullbackModules).map
          (HomologicalComplex.ιMapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
              p q n hpq) ≫
        (pullbackTensorTotalIso g K L).hom.f n =
      (Stacks.SheafOfModules.pullbackTensorIso g).hom.app (K.X p, L.X q) ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplexFunctor g).obj K)
          ((pullbackComplexFunctor g).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)
            p q n hpq :=
  ι_pullbackTensorTotalIso_hom g K L p q n hpq

/-- **The comparison of Stacks 03EL for the four-field pullback, followed by an isomorphism of
each tensor factor, read on the summand of bidegree `(p, q)`.** It is the comparison of
Stacks 03EL in that bidegree, followed by the two factor isomorphisms in that bidegree and the
summand inclusion of the target.

The two factor isomorphisms are left abstract — `K'` and `L'` are arbitrary complexes — which is
what keeps every object in this statement spelled one way, so that the rewrites of the proof find
their patterns. -/
private lemma ι_comp_mapBifunctorMapIso
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (K' L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (eK : (pullbackComplexFunctor g).obj K ≅ K')
    (eL : (pullbackComplexFunctor g).obj L ≅ L')
    (p q n : ℤ) (hpq : p + q = n) :
    (g.pullbackModules).map
          (HomologicalComplex.ιMapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
              p q n hpq) ≫
        ((pullbackTensorTotalIso g K L).hom.f n ≫
          (mapBifunctorMapIso (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            eK eL).hom.f n) =
      (Stacks.SheafOfModules.pullbackTensorIso g).hom.app (K.X p, L.X q) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map (eK.hom.f p)).app
              (((pullbackComplexFunctor g).obj L).X q) ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (K'.X p)).map
            (eL.hom.f q) ≫
            HomologicalComplex.ιMapBifunctor K' L'
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) p q n hpq)) :=
  comp_comp_of_comp_eq
    (congrArg (fun morphism => HomologicalComplex.Hom.f morphism n)
      (mapBifunctorMapIso_hom (sheafTensor.{u, u, u, u, u} X.O) eK eL))
    (ι_pullbackTensorTotalIso_hom' g K L p q n hpq)
    (HomologicalComplex.ι_mapBifunctorMap eK.hom eL.hom
      (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) p q n hpq)

/-! ## The two presentations of the morphism of topoi agree -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The morphism of topoi underlying the four-field morphism of ringed topoi is the morphism of
topoi of the associated morphism of ringed sites.** True by definition.

It is not obvious that this should be definitional:
`modulesHomOfSiteHom` goes through `AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom`, its
`ringedToposHom` and then `toRingedToposModulesHom`, and the morphism of topoi survives all three
unchanged. The consequence is that every lemma about the direct image of a morphism of *ringed
sites* — in particular
`AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map`, which says that the direct
image is the identity on sections — applies verbatim to the `f_*` that the chain of Stacks 03EL
leaves standing. -/
lemma modulesHomOfSiteHom_toToposHom (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (modulesHomOfSiteHom f hmos).toToposHom =
      (RingedSite.Hom.ofRingedToposSiteHom f hmos).toposHom :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The continuous functor of the associated morphism of ringed sites is the continuous functor one
started with. True by definition; recorded because the object `f.u(U)` over which the sections of a
direct image live is spelled through it. -/
lemma ofRingedToposSiteHom_u (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (RingedSite.Hom.ofRingedToposSiteHom f hmos).u = f.u :=
  rfl

/-! ## The module-level comparison for the site-presented pullback -/

/-- **The comparison `f^*(A ⊗_{𝒪_D} B) ⟶ f^*A ⊗_{𝒪_C} f^*B` for the site-presented pullback.**

It is the comparison of Stacks 03EL for the four-field pullback of Stacks 03D6,
`Stacks.SheafOfModules.pullbackTensorIso`, transported along the identification
`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso` of the two pullbacks — on the source
once, and in each tensor factor of the target. This is the summandwise content of
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`, by
`ι_pullbackToposTensorTotalIso_hom`. -/
def pullbackToposTensorMap (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.pullbackTopos.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (f.pullbackTopos.obj A)).obj
        (f.pullbackTopos.obj B) :=
  (pullbackModulesSiteIso f hmos).inv.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≫
    (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app (A, B) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
        ((pullbackModulesSiteIso f hmos).hom.app A)).app
      (((modulesHomOfSiteHom f hmos).pullbackModules).obj B) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
        (f.pullbackTopos.obj A)).map ((pullbackModulesSiteIso f hmos).hom.app B)

/-- The comparison at the modules of a fixed bidegree of two complexes, written with the degrees
of the pullback complexes rather than with the pullbacks of the degrees.

The two spellings are definitionally equal, and `pullbackToposTensorMapDeg_eq` records that this
is `pullbackToposTensorMap` at `(K^p, L^q)`. Writing it out again at the second spelling is
forced rather than chosen: the summand inclusion of the total complex of the pullbacks has its
source spelled with the degrees of the pullback complexes, and a composite whose seam carries
the two spellings is one in which `rw` cannot find the associativity pattern — the unifier has
to decide the equality of the two spellings of the seam object, and deciding it means unfolding
the sheaf tensor product. -/
def pullbackToposTensorMapDeg (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (p q : ℤ) :
    f.pullbackTopos.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj (K.X p)).obj
          (L.X q)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (((pullbackComplex f).obj K).X p)).obj
        (((pullbackComplex f).obj L).X q) :=
  (pullbackModulesSiteIso f hmos).inv.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj (K.X p)).obj (L.X q)) ≫
    (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app
      (K.X p, L.X q) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
        (((pullbackComplexSiteIso f hmos).app K).hom.f p)).app
      (((pullbackComplexFunctor (modulesHomOfSiteHom f hmos)).obj L).X q) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
        (((pullbackComplex f).obj K).X p)).map
      (((pullbackComplexSiteIso f hmos).app L).hom.f q)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The degreewise comparison is the module-level comparison at the modules of that bidegree. -/
lemma pullbackToposTensorMapDeg_eq (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (p q : ℤ) :
    pullbackToposTensorMapDeg f hmos K L p q =
      pullbackToposTensorMap f hmos (K.X p) (L.X q) :=
  rfl

private lemma pullbackToposTensorTotalIso_hom_f (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (n : ℤ) :
    (pullbackToposTensorTotalIso f hmos K L).hom.f n =
      (pullbackModulesSiteIso f hmos).inv.app
          ((HomologicalComplex.mapBifunctor K L (sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ)).X n) ≫
        (pullbackTensorTotalIso (modulesHomOfSiteHom f hmos) K L).hom.f n ≫
          (mapBifunctorMapIso (sheafTensor.{u, u, u, u, u} X.O)
            ((pullbackComplexSiteIso f hmos).app K)
            ((pullbackComplexSiteIso f hmos).app L)).hom.f n :=
  rfl

/-- **The comparison of total tensor complexes for the site-presented pullback acts on the
summand of bidegree `(p, q)` by the module-level comparison.**

This is the analogue for the site-presented pullback of
`Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom`. -/
theorem ι_pullbackToposTensorTotalIso_hom (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
            p q n hpq) ≫
        (pullbackToposTensorTotalIso f hmos K L).hom.f n =
      pullbackToposTensorMapDeg f hmos K L p q ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)
            p q n hpq := by
  let inclusion := HomologicalComplex.ιMapBifunctor K L
    (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) p q n hpq
  let comparison := (pullbackTensorTotalIso (modulesHomOfSiteHom f hmos) K L).hom.f n
  let factorMap := (mapBifunctorMapIso (sheafTensor.{u, u, u, u, u} X.O)
    ((pullbackComplexSiteIso f hmos).app K) ((pullbackComplexSiteIso f hmos).app L)).hom.f n
  let moduleComparison := (Stacks.SheafOfModules.pullbackTensorIso
    (modulesHomOfSiteHom f hmos)).hom.app (K.X p, L.X q)
  let leftMap := ((sheafTensor.{u, u, u, u, u} X.O).map
    (((pullbackComplexSiteIso f hmos).app K).hom.f p)).app
      (((pullbackComplexFunctor (modulesHomOfSiteHom f hmos)).obj L).X q)
  let rightMap := ((sheafTensor.{u, u, u, u, u} X.O).obj
    (((pullbackComplex f).obj K).X p)).map (((pullbackComplexSiteIso f hmos).app L).hom.f q)
  let targetInclusion := HomologicalComplex.ιMapBifunctor
    ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
    (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) p q n hpq
  exact (congrArg (fun morphism => f.pullbackTopos.map inclusion ≫ morphism)
    (pullbackToposTensorTotalIso_hom_f f hmos K L n)).trans
      (naturality_comp_comparison (pullbackModulesSiteIso f hmos).inv inclusion
        comparison factorMap moduleComparison leftMap rightMap targetInclusion
        (ι_comp_mapBifunctorMapIso (modulesHomOfSiteHom f hmos) K L
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          ((pullbackComplexSiteIso f hmos).app K)
          ((pullbackComplexSiteIso f hmos).app L) p q n hpq))

/-! ## The right-unitor coherence -/

/-- **The module-level right-unitor coherence for the site-presented pullback**, written out as a
proposition: the comparison `f^*(A ⊗_{𝒪_D} 𝒪_D) ⟶ f^*A ⊗_{𝒪_C} f^*𝒪_D`, followed by `𝟙 ⊗ ν` for
the unit comparison `ν : f^*𝒪_D ⟶ 𝒪_C` of `SheafOfModules.pullbackObjUnitToUnit` and by the right
unitor of `Stacks.SheafOfModules.sheafTensorUnitNatIso`, is the pullback of the right unitor.

It is the module-level input of the right-unitor coherence of Stacks 07A4, hence of the base case
of Stacks 0944 at `K = 𝒪_D[n]`. It is proved by
`Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposRightUnitorCoherence`;
the same coherence for this library's own comparison and unit comparison is
`Stacks.SheafOfModules.RingedToposPullback.rightUnitality`. -/
def PullbackToposRightUnitorCoherence (hmos : f.u.IsMorphismOfSites Y.J X.J) : Prop :=
  ∀ A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
    pullbackToposTensorMap f hmos A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (f.pullbackTopos.obj A)).map
            (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) ≫
          (Stacks.SheafOfModules.sheafTensorUnitNatIso X.O).hom.app (f.pullbackTopos.obj A) =
      f.pullbackTopos.map
        ((Stacks.SheafOfModules.sheafTensorUnitNatIso Y.O).hom.app A)

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
