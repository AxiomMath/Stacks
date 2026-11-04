module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor

/-!
# The comparison of Stacks 03EL against a transition of pullbacks of ringed topoi

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` and
`χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)` be morphisms of ringed topoi and let

`θ : ψ^* ⋙ φ^* ⟶ χ^*`

be a *transition*: a natural transformation comparing the iterated pullback of sheaves of modules
with the pullback along `χ`. Each of the three morphisms carries the comparison of
**Stacks 03EL**, `Stacks.SheafOfModules.pullbackTensorIso`, and this file names the compatibility
of `θ` with the three comparisons — the tensorator half of the statement that `θ` is a *monoidal*
natural transformation — and records its two equivalent forms.

The statement is the exact topos analogue of
`Stacks.PullbackTensorComposition.comparison_comp`, which proves the same compatibility for
morphisms of ringed *spaces* and for the transition
`Stacks.DerivedPullback.Composition.modulePullbackComp`. Here it is a hypothesis and not a
theorem; the implementation notes record why, and `θ` is kept an arbitrary natural transformation
rather than the component of
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`, because the transitions that arise in
practice — the pullback transition of Stacks 09WF between the restrictions of a sheaf of modules
to two simplicial components, for instance — are not isomorphisms and do not come from a
factorisation `χ = ψ ∘ φ` of morphisms of ringed topoi.

## Main definitions

* `Stacks.SheafOfModules.PullbackTensorTransitionCoherence`: **the compatibility of a transition
  of pullbacks with the comparison of Stacks 03EL.**

## Main results

* `Stacks.SheafOfModules.pullbackTensorIso_inv_comp_app_of_transitionCoherence`: the same
  compatibility with the comparison of `ψ` inverted, which is the form a consumer that builds a
  map *into* a pullback of a tensor product needs.

## Implementation notes

*Why this is a hypothesis.* `Stacks.SheafOfModules.pullbackTensorIso` is produced from the
six-step chain of bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv`, and the only
characterisation it carries is that the chain sends it to the identity
(`Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp`). Composing that
characterisation for `χ` out of the ones for `φ` and `ψ` needs each of the six steps to have a
composition law, and all six now have one: `Stacks.SheafOfModules.pullbackTensorStep1_comp'`
through `…Step5_comp`, in the five files
`StacksDraft/Algebra/Category/ModuleCat/Sheaf/PullbackTensorStep⟨i⟩StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf/CompositionLaw.lean`, and for
the sixth step `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq_comp` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtendScalarsTensorCompositionLaw.lean`. The three
paragraphs below describe what shape each of them takes and what they rest on.

Those six are still not a proof of the coherence stated here, and the gap between them and it is
not one of further bookkeeping. Each of the six is a law at the *composite* morphism of ringed
topoi `ψ ∘ φ` and at the *canonical* comparisons attached to it — the compositor
`Stacks.SheafOfModules.pullbackModulesCompAdjIso` of pullbacks, the comparison
`…pushforwardModulesCompAppIso` of direct images, the comparison
`Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso` of the two readings of
`(ψ ∘ φ)⁻¹O_E`. So what they can give, once assembled, is the coherence for the one transition
`θ = (pullbackModulesCompAdjIso φ ψ).inv`, at `χ = ψ ∘ φ`; the `θ` of this file is arbitrary, and
the consumers that motivated it instantiate it at a `θ` which is *not* that one. The leading
consumer is `CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence`: there `χ` is the
degree-`m` component inclusion `g_m`, `ψ ∘ φ` is `g_n ∘ f_φ`, and the two are compared by the
2-morphism `CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism` of Stacks 04IC,
which is *not* invertible — the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationRingedTwoIso.lean`
record that it becomes invertible only after a ringed augmentation is appended, by Stacks
0D7H (1). Closing that gap needs a law for the comparison of Stacks 03EL in the *2-morphism*
variable — a compatibility of
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` with `pullbackTensorIso` at its
two parallel morphisms — and that law is available:
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackTensorIso_hom_app_comp_pullbackModulesMap`
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorTwoMorphismMonoidal`, which assumes
no invertibility. It is not an instance of this file's coherence — a 2-morphism relates two
parallel morphisms, where this file's `θ` relates an iterated pullback to a single one — but it
combines with it:
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorTransitionTwoMorphism`, is the
statement that the coherence of this file is stable under composing `θ` with the transformation of
pullbacks induced by a 2-morphism. So for every `θ` that arises from a factorisation and a
2-morphism — which is every `θ` the consumers supply — the single input still owed is the
coherence for the one transition `θ = (pullbackModulesCompAdjIso φ ψ).inv` at `χ = ψ ∘ φ`: the
assertion that the compositor of Stacks 03D8 is monoidal.

The third step, the transport of bilinear pairings of Stacks 03D3
(`Stacks.SheafOfModules.inverseImageBilinearEquiv`), does now have one:
`Stacks.SheafOfModules.inverseImageBilinearEquiv_comp`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearCompositionLaw`. It rests on the
identification of the inverse image of a composite of morphisms of topoi with the composite of
the inverse images — `MorphismOfTopoi.inverseImageCompIso`, the law the bijection is actually
read through being `MorphismOfTopoi.comp_homEquiv_prodComparison` — in
`StacksFrontier.CategoryTheory.Sites.Topos.InverseImageComp`.

The second and the fourth step have theirs too, and neither is an equation between two
bijections, because neither step has two bijections to compose: each is a single universal
property of a tensor product, and all a composite supplies is a comparison of the data that
universal property is taken at. `Stacks.SheafOfModules.pullbackTensorStep2_comp'` is the
compatibility of the one universal property over `O_E` with the comparison
`ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of successive direct images, and
`Stacks.SheafOfModules.pullbackTensorStep4_comp` is the compatibility of the one universal
property over `(ψ ∘ φ)⁻¹O_E` with the comparison
`Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso` of that base ring with the
iterated inverse image `φ⁻¹ψ⁻¹O_E`. The law in the ring variable that the latter is read through
is `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_restrictScalars`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariable`; step 4 is the one step of
the six at which a comparison of base rings cannot be avoided, step 2 taking its ring from the
target, which a composite shares with its second factor.

Two things that law does *not* supply, and that a composite characterisation would still need.
First, it is a law on the *value* of the bijection, stated in the single spelling `χ⁻¹` of the
inverse image of the composite, and not an equation between the bijection for `χ` and the
composite of the bijections for `φ` and `ψ`: those two have types that meet only after a
restriction of scalars along `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso`, since
`φ⁻¹ψ⁻¹O` and `χ⁻¹O` are distinct sheaves of rings with the same underlying sheaf of sets, and
elaborating the composed form in that shape exhausts the heartbeat budget at `whnf`.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DirectImageCompositionLaw.lean` records what cures
that particular failure, having had to cure it: name the endpoint objects, and supply every
reassociation and every merge of two restrictions of scalars as a statement about abstract
functors rather than leaving it definitional.

Second, the composed form also needs a composition law for the *direct* image of sheaves of
modules along morphisms of topoi — `Stacks.Sheaves.RingedToposModules.directImageModules` of a
composite. That one now exists:
`Stacks.Sheaves.RingedToposModules.directImageModulesCompIso`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageCompositionLaw`, with the ring-level law
it rests on — the unit of a composite is the composite of the units — as
`Stacks.Sheaves.RingedToposModules.ringUnitComp_eq`. It is stated for `directImageModules`
itself, so it is not one of the comparisons that were stated only for the four-field
`RingedToposHom` and its `pushforwardModules`
(`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` and
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`), neither of which covers the
restriction of scalars along the unit `O ⟶ f_*f⁻¹O` that `directImageModules` is defined by.

Both of those concern the *third* step only. Steps 1, 5 and 6 have composition laws of their own.
`Stacks.SheafOfModules.pullbackTensorStep1_comp'` splits step 1 for the composite into step 1 for
`ψ` and a transposition across the adjunction of Stacks 03D7 for `φ`, read against the compositor
of pullbacks and the comparison of direct images; its conclusion is literally the shape step 2's
law consumes, so steps 1, 2 and 3 chain with no adapter.
`Stacks.SheafOfModules.pullbackTensorStep5_comp` factors the extension-restriction adjunction of
Stacks 03CZ for the composite base-ring map through the two factors, routed through
`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` and the ring-level law
`Stacks.SheafOfModules.fSharpCommRing_comp`; and
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq_comp` is the law for step 6.

One obstacle to assembling the six is worth recording, because it is not visible from the list of
names. The laws for steps 1, 2, 3 and 5 determine the step at the composite — their conclusion has
the step applied to the composite alone on one side — while the law for step 4 does not: its
conclusion equates `tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) … ≫
(restrictScalars …).map (pullbackTensorStep4 (ψ.comp φ) … q)` with the image of the same pairing
over the iterated base ring. Solving it for `pullbackTensorStep4 (ψ.comp φ) … q` needs
`Stacks.SheafOfModules.tensorSheafRestrictScalarsHom` to be invertible at the base-ring
comparison, which is an isomorphism of sheaves of rings; that invertibility is
`Stacks.SheafOfModules.isIso_tensorSheafRestrictScalarsHom`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BilinearRingVariableIso.lean`. With it, and with
the faithfulness of restriction of scalars, step 4 at the composite *is* determined by its law:
`Stacks.SheafOfModules.pullbackTensorStep4_comp_eq`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorStep4CompositionSolved.lean`. So this
obstacle is gone, and what is left between the six laws and the compositor case is the assembly
itself.

*Why the proof for ringed spaces does not transfer.*
`Stacks.PullbackTensorComposition.comparison_comp` is proved by
`Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext`: two morphisms out of the pullback of a
tensor product of sheaves of modules on a ringed *space* agree as soon as they agree on the
images under `AlgebraicGeometry.PresheafOfModules.pullbackUnit` of the local pure tensors, and
there the comparison is computed by
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`. Both of those rest on the pullback along
a morphism of ringed spaces being the sheafification of a presheaf-level construction indexed by
the opens, through `AlgebraicGeometry.PresheafOfModules.opensMap`. For a morphism of ringed topoi
the inverse image is the abstract one of Stacks 03D2, which is not the sheafification of any
presheaf-level functor — the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ChangeOfRingsMonoidal.lean` record this as the
reason the pullback of modules along a morphism of ringed topoi is not made monoidal there — so
there is no `pullbackUnit`, no extensionality principle of that shape, and no section-level
formula for the comparison to be evaluated by.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Transition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (θ : ψ.pullbackModules ⋙ φ.pullbackModules ⟶ χ.pullbackModules)

/-- **The compatibility of a transition of pullbacks of sheaves of modules with the comparison of
Stacks 03EL.** For sheaves of `O_E`-modules `A` and `B`, the transition at `A ⊗_{O_E} B` followed
by the comparison for `χ` is the pullback along `φ` of the comparison for `ψ`, followed by the
comparison for `φ`, followed by the transition in each tensor factor.

This is the tensorator half of the assertion that `θ` is a monoidal natural transformation; the
unit half is a separate statement and is not used by the consumers of this one. It is the exact
analogue, for morphisms of ringed topoi, of
`Stacks.PullbackTensorComposition.comparison_comp` for morphisms of ringed spaces, and it is
*not* proved in this development: the module docstring records what a proof would need and why
the ringed-space proof does not transfer. -/
def PullbackTensorTransitionCoherence : Prop :=
  ∀ A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O),
    θ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (A, B)) ≫
        (pullbackTensorIso χ).hom.app (A, B) =
      (φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (A, B)) ≫
        (pullbackTensorIso φ).hom.app ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
            ((θ.app A, θ.app B) :
              (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
                  (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))

/-- **The coherence of a transition with the comparison of Stacks 03EL, with the comparison for
`ψ` inverted.** The pullback along `φ` of the inverse comparison for `ψ`, followed by the
transition at `A ⊗_{O_E} B` and then the comparison for `χ`, is the comparison for `φ` followed
by the transition in each tensor factor.

This is the form in which the coherence is consumed: a map built out of the *inverse* comparison
— as the adjunct of the canonical map of Stacks 0D9E (2) is — meets the transition in this
shape. -/
theorem pullbackTensorIso_inv_comp_app_of_transitionCoherence
    (h : PullbackTensorTransitionCoherence φ ψ χ θ)
    (A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (φ.pullbackModules).map ((pullbackTensorIso ψ).inv.app (A, B)) ≫
        θ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (A, B)) ≫
          (pullbackTensorIso χ).hom.app (A, B) =
      (pullbackTensorIso φ).hom.app ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          ((θ.app A, θ.app B) :
            (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
                (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
              ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)) := by
  refine Eq.trans (congrArg (fun k =>
    (φ.pullbackModules).map ((pullbackTensorIso ψ).inv.app (A, B)) ≫ k) (h A B)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫
    ((pullbackTensorIso φ).hom.app ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
        ((θ.app A, θ.app B) :
          (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))))
    (Eq.trans ((φ.pullbackModules).map_comp _ _).symm
      (Eq.trans (congrArg (φ.pullbackModules).map ((pullbackTensorIso ψ).inv_hom_id_app (A, B)))
        ((φ.pullbackModules).map_id _)))) ?_
  exact Category.id_comp _

end Transition

end Stacks.SheafOfModules

end
