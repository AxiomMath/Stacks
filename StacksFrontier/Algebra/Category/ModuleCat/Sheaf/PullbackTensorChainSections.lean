module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearCompositionLaw
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-! # The chain of bijections of Tag 03EL on a pure tensor

The comparison of **Tag 03EL** `f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G` is the preimage of the
identity under the six-step chain `Stacks.SheafOfModules.pullbackTensorHomEquiv`, and the only
things known about it are that the chain carries it to the identity and that it is natural. Any
compatibility of it with a structural morphism — a unitor, the associator — has to start from a
formula saying what it does to a *local section*, and that means evaluating the chain.

This file evaluates the bottom of the chain. `StacksDraft.…​.ExtendScalarsTensorSections` supplies
steps 5 and 6 on a pure tensor; here steps 4, 5, 6 are composed into a value formula for the
pairing at the bottom, and steps 2 and 3 are composed into a value formula for the morphism
`F ⊗_{O_D} G ⟶ f_*N` the top of the chain produces. What is left between them is the topos unit of
`f⁻¹ ⊣ f_*`, which is where the computation must stop for an abstract morphism of topoi and which
a site-presented one strips; see `AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map`
below.

## Main results

* `Stacks.SheafOfModules.tensorSheaf_hom_ext`: **two morphisms of sheaves of modules out of a
  tensor product sheaf agree as soon as they agree on the sheafification-unit images of pure
  tensors.** This is the extensionality principle every statement about the comparison of
  Tag 03EL on sections is proved by. It is the sheafification adjunction followed by
  `ModuleCat.MonoidalCategory.tensor_ext`, and it is strictly weaker machinery than
  `Stacks.SheafOfModules.pairing_ext`: no bilinearity is mentioned.
* `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app`: **the unit of the
  adjunction of Stacks 03D7 factors through the topos unit and the unit of extension of
  scalars.** The adjunction is by definition the composite of the adjunction of Stacks 03D3 with
  the adjunction of Stacks 03CZ, so this is `CategoryTheory.Adjunction.comp_unit_app`; it is the
  identity that puts the left-hand side of a unitor coherence into the shape the chain produces.
* `AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map`: **the direct image of a
  morphism of sheaves of sets along a morphism of ringed *sites* is that morphism, on sections.**
  Sections over `Z` of `f_*S` are sections over `f.u(Z)` of `S` on the nose, because
  `AlgebraicGeometry.RingedSite.Hom.sectionsComparison` is the identity in every component. This
  is what lets the `f_*` that
  `Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv` leaves standing be removed. For an
  abstract `CategoryTheory.Sheaf.MorphismOfTopoi` there is no such formula — but there is none for
  `f⁻¹` even here, which is why the topos unit survives in every formula below.
* `AlgebraicGeometry.RingedSite.unitProdSection_prodComparison`: **the product comparison of
  `f⁻¹` carries the unit image of a pair of local sections to the pair of their unit images.** This
  is what turns step 3 of the chain into "evaluate the pairing upstairs at the two unit images",
  and with it the topos unit is the only thing the chain leaves in the answer.
* `Stacks.SheafOfModules.pairingApp_pullbackTensorBottom`: **steps 4, 5 and 6 of the chain on a
  pure tensor.** The pairing at the bottom of the chain pairs two local sections of `f⁻¹F` and
  `f⁻¹G` by sending them to the sheafification-unit image of the pure tensor of their images under
  the unit of extension of scalars — that is, to the pure tensor of their images in
  `f^*F ⊗_{O_C} f^*G`. No scalar is left over.
* `Stacks.SheafOfModules.pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul`: **steps 2 and 3 of
  the chain on a pure tensor.** The morphism `F ⊗_{O_D} G ⟶ f_*N` that steps 2 and 3 produce from a
  pairing `q` upstairs carries the unit image of `a ⊗ₜ r` to the pair `(a, r)` pushed through the
  topos unit and then through the direct image of `q` precomposed with the product comparison of
  `f⁻¹`.

## Implementation notes

**The seam at the target of the chain, and how it is crossed.** Step 6 of the chain has its target
spelled `(Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))` applied to the
pair of pullbacks, while `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` — which *is*
step 6 — has its target spelled `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.O.obj _`
applied to the two extensions of scalars. Both unfold to the sheafification of the same objectwise
tensor product, so they are definitionally equal; but a `rw` whose motive mentions the second in a
goal written with the first is reported ill-typed at `implicit` transparency.
`Stacks.SheafOfModules.pullbackTensorTarget` is that object declared once, in the second spelling,
and `Stacks.SheafOfModules.pullbackTensorBottomHom` is steps 5 and 6 at the identity declared once
with that as its target. Declaring them absorbs the definitional equality into a declared type,
which is the move this development prescribes for the seams of a composite, and it is what makes
the value formulas below ordinary rewrites.

**The elaborator has a budget, and this is where it is spent.** Writing the composite
`step4.symm (step5.symm (step6.symm (𝟙 _)))` out inside the statement of a value formula — rather
than naming `pullbackTensorBottomHom` first — exhausts the default heartbeat budget at `whnf`
before the statement is even elaborated. Naming the two intermediate objects brings the same
statement down to about a second. No heartbeat budget is raised anywhere in this file.

**Why `pullbackTensorTarget` is an `abbrev` and `pullbackTensorBottomHom` a `def`.** The target has
to stay reducible, because the chain's own types mention it in the other spelling and unification
must be allowed to see through the name; the morphism does not, and leaving it opaque is what
keeps the value formulas cheap.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe w v u

namespace Stacks.SheafOfModules

section Ext

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} {hA : Presheaf.IsSheaf J (ringPresheaf A)}
  {F G N : SheafOfModules.{w} (commRingSheaf J A hA)}

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Two morphisms of sheaves of modules out of a tensor product sheaf agree as soon as they agree
on the sheafification-unit images of pure tensors.**

The tensor product sheaf is the sheafification of the objectwise tensor product, so a morphism out
of it is determined by its restriction along the sheafification unit — that is the hom-set
bijection `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom` — and a morphism of
presheaves of modules out of an objectwise tensor product is determined by its values on pure
tensors.

This is the extensionality principle that every statement about the comparison of Tag 03EL on local
sections is proved by. It asks for less than `Stacks.SheafOfModules.pairing_ext`: bilinearity is
not mentioned, because the sheafification adjunction already has the morphisms in hand. -/
lemma tensorSheaf_hom_ext
    {m m' : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G) ⟶ N}
    (hyp : ∀ (U : Cᵒᵖ) (a : F.val.obj U) (b : G.val.obj U),
      m.val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A hA) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
            (a ⊗ₜ[(ringPresheaf A).obj U] b)) =
        m'.val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A hA) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
            (a ⊗ₜ[(ringPresheaf A).obj U] b))) :
    m = m' := by
  apply (tensorSheafHomEquivPresheafTensorHom (F := F) (G := G) (N := N)).injective
  rw [tensorSheafHomEquivPresheafTensorHom_apply, tensorSheafHomEquivPresheafTensorHom_apply]
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  exact (CategoryTheory.comp_apply _ _ _).trans
    ((hyp U a b).trans (CategoryTheory.comp_apply _ _ _).symm)

end Ext

end Stacks.SheafOfModules

namespace Stacks.Sheaves.RingedToposModules

section Unit

universe w' v' u' w₂ v₂ u₂

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **The unit of the adjunction of Stacks 03D7 factors through the topos unit and the unit of
extension of scalars.** `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` is by
definition the composite of the adjunction of Stacks 03D3 — inverse image against direct image of
sheaves of modules — with the adjunction of Stacks 03CZ, so its unit at `A` is the topos-level unit
at `A` followed by the direct image of the extension-of-scalars unit at `f⁻¹A`. This is
`CategoryTheory.Adjunction.comp_unit_app`, named here because it is the identity that puts the
left-hand side of a unitor coherence into the shape the chain of Tag 03EL produces: the chain
delivers the two units separately, and the coherence is stated with the one unit of Stacks 03D7.

Combined with
`…RingedToposModules.moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app'`,
which says the first factor is the unit of `f⁻¹ ⊣ f_*` on underlying sheaves of sets, and with
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`, which
computes the second on sections, this reads the unit of Stacks 03D7 on a local section. -/
lemma pullbackAdjPushforwardModules_unit_app
    (A : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackAdjPushforwardModules f).unit.app A =
      (inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app A ≫
        (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)) :=
  Adjunction.comp_unit_app _ _ A

end Unit

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedSite

section Sections

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- **The direct image along a morphism of ringed sites is the identity on sections.** For a
morphism `f` of ringed sites and a morphism `m` of sheaves of sets on the source, the sections over
`Z` of `f_*m` are the sections over `f.u(Z)` of `m`: the direct image of the morphism of topoi is
restriction along `f.u`, so `f_* ⋙ sections over Z` is `sections over f.u(Z)` on the nose. This is
`AlgebraicGeometry.RingedSite.Hom.sectionsComparison`, whose every component is the identity and
whose naturality is `rfl`, read as an equation between the two maps on sections.

It is what removes the `f_*` that `Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv`
leaves standing: for an abstract `CategoryTheory.Sheaf.MorphismOfTopoi` the direct image has no
description on sections, but for the topos morphism of a morphism of sites it has this one. Note
that `f⁻¹` still has none — a morphism of sites presents the inverse image as a sheafified left
Kan extension — so the unit of `f⁻¹ ⊣ f_*` survives in every value formula of this file, and that
is not a defect of the formulas but the shape of Tag 03D3. -/
lemma sectionsFunctor_map_pushforward_map (Z : Y.Cᵒᵖ) {S T : Sheaf X.J (Type u)} (m : S ⟶ T)
    (z : (Sheaf.sectionsFunctor Y.J Z).obj (f.toposHom.pushforward.obj S)) :
    (Sheaf.sectionsFunctor Y.J Z).map (f.toposHom.pushforward.map m) z =
      (Sheaf.sectionsFunctor X.J (f.u.op.obj Z)).map m z := rfl

/-- **The unit of `f⁻¹ ⊣ f_*` on a local section, declared at the source-site spelling.** For a
morphism `f` of ringed sites and a local section `a` of a sheaf of sets `S` over `U`, this is the
image of `a` under the unit, read as a section of `f⁻¹S` over `f.u(U)` rather than as a section of
`f_*f⁻¹S` over `U`.

The two are the same element and the two types are definitionally equal, by
`sectionsFunctor_map_pushforward_map`; but they are equal only at *default* transparency, so a goal
carrying both is not type-correct at `implicit` transparency and `rw` reports a pattern it cannot
find. Declaring the element once at the source-site spelling absorbs that definitional equality
into a declared type, which is the move this development prescribes for the seams of a composite,
applied here to an element rather than to a morphism. Without it `unitProdSection_prodComparison`
below cannot be stated in a form `rw` will work in. -/
def unitSection (S : Sheaf Y.J (Type u)) (U : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor Y.J U).obj S) :
    (Sheaf.sectionsFunctor X.J (f.u.op.obj U)).obj (f.toposHom.inverseImage.obj S) :=
  (Sheaf.sectionsFunctor Y.J U).map (f.toposHom.adj.unit.app S) a

/-- **The unit of `f⁻¹ ⊣ f_*` on a pair of local sections, declared at the source-site spelling.**
The pair `(a, r)`, read as a section of the product and pushed through the unit, as a section of
`f⁻¹(S_F ⨯ S_G)` over `f.u(U)`. This is the element the pairing produced by step 3 of the chain of
Tag 03EL is evaluated at; see `unitProdSection_prodComparison`. -/
def unitProdSection (SF SG : Sheaf Y.J (Type u)) (U : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor Y.J U).obj SF) (r : (Sheaf.sectionsFunctor Y.J U).obj SG) :
    (Sheaf.sectionsFunctor X.J (f.u.op.obj U)).obj
      (f.toposHom.inverseImage.obj (SF ⨯ SG)) :=
  (Sheaf.sectionsFunctor Y.J U).map (f.toposHom.adj.unit.app (SF ⨯ SG))
    (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} Y.J U) (A := SF) (B := SG) a r)

/-- **The product comparison of `f⁻¹` carries the unit image of a pair of sections to the pair of
their unit images.**

This is the fact that closes the gap left by
`Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv`, which transports a pair of local
sections through the topos unit and then through the direct image of a pairing *precomposed with
the product comparison of `f⁻¹`*: the statement here says that the product comparison does the
only thing it could, namely take the unit image of `(a, r)` to the pair of the unit images of `a`
and of `r`. Composing it with the formula for the pairing therefore turns step 3 of the chain of
Tag 03EL into "evaluate the pairing upstairs at the two unit images".

It is the naturality of the unit at the two projections, read on sections, together with
`AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map` to strip the direct image. The
two `change` steps in the proof are where the direct image is stripped: `change` works at default
transparency, where the stripping is `rfl`, whereas a `rw` at that point is reported ill-typed at
`implicit` transparency. -/
lemma unitProdSection_prodComparison (SF SG : Sheaf Y.J (Type u)) (U : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor Y.J U).obj SF) (r : (Sheaf.sectionsFunctor Y.J U).obj SG) :
    (Sheaf.sectionsFunctor X.J (f.u.op.obj U)).map
        (Limits.prodComparison f.toposHom.inverseImage SF SG)
        (unitProdSection f SF SG U a r) =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} X.J (f.u.op.obj U))
        (A := f.toposHom.inverseImage.obj SF) (B := f.toposHom.inverseImage.obj SG)
        (unitSection f SF U a) (unitSection f SG U r) := by
  have key : ∀ {T : Sheaf Y.J (Type u)} (p : SF ⨯ SG ⟶ T),
      (Sheaf.sectionsFunctor X.J (f.u.op.obj U)).map (f.toposHom.inverseImage.map p)
          (unitProdSection f SF SG U a r) =
        (Sheaf.sectionsFunctor Y.J U).map (f.toposHom.adj.unit.app T)
          ((Sheaf.sectionsFunctor Y.J U).map p
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} Y.J U) (A := SF) (B := SG) a r)) :=
    fun {T} p ↦ by
      change (Sheaf.sectionsFunctor Y.J U).map (f.toposHom.pushforward.map
          (f.toposHom.inverseImage.map p))
        ((Sheaf.sectionsFunctor Y.J U).map (f.toposHom.adj.unit.app (SF ⨯ SG))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} Y.J U) (A := SF) (B := SG) a r)) = _
      rw [← Functor.map_comp_apply, ← Functor.comp_map, ← f.toposHom.adj.unit.naturality p,
        Functor.map_comp_apply, CategoryTheory.Functor.id_map]
  refine Functor.prodObjMk_ext (P := Sheaf.sectionsFunctor.{u} X.J (f.u.op.obj U))
    (A := f.toposHom.inverseImage.obj SF) (B := f.toposHom.inverseImage.obj SG) ?_ ?_
  · rw [Functor.map_fst_prodObjMk, ← Functor.map_comp_apply, Limits.prodComparison_fst, key,
      Functor.map_fst_prodObjMk]
    rfl
  · rw [Functor.map_snd_prodObjMk, ← Functor.map_comp_apply, Limits.prodComparison_snd, key,
      Functor.map_snd_prodObjMk]
    rfl

end Sections

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

section Chain

universe w' v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The sheaf of values at which the chain of Tag 03EL is read**, namely `f^*F ⊗_{O_C} f^*G`,
spelled as a tensor product sheaf over the structure sheaf of the source *written as a presheaf of
commutative rings*.

This is `((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj` applied to
`((f.pullbackModules).obj F, …)`, the spelling of step 6's target; the two unfold to the
sheafification of the same objectwise tensor product and are definitionally equal. Declaring the
object once at this spelling is what lets
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, which is stated here, be composed with
the chain, which is stated there. It is an `abbrev` on purpose: the chain's own types mention the
object in the other spelling, so unification has to be allowed to see through the name. -/
abbrev pullbackTensorTarget : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj ((extendScalarsFSharp f).obj
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F))).obj
    ((extendScalarsFSharp f).obj
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))

/-- **Steps 5 and 6 of the chain of Tag 03EL at the identity**, declared once with its target at
the spelling of `pullbackTensorTarget`.

It is the morphism `f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G ⟶ (f^*F ⊗_{O_C} f^*G)|_{f⁻¹O_D}` the bottom two steps
produce, and by `pullbackAdjPushforwardModules_unit_app`'s second factor together with
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` it is the unit of extension of scalars
followed by the base-change comparison; `pairingApp_pullbackTensorBottom` is its value on a pure
tensor. Unlike `pullbackTensorTarget` this is a `def`: nothing needs to unfold it, and leaving it
opaque is what keeps the value formulas inside the elaborator's budget. -/
def pullbackTensorBottomHom :
    inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj
        (pullbackTensorTarget f F G) :=
  (pullbackTensorStep5 f F G (pullbackTensorTarget f F G)).symm
    ((pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
      (𝟙 (pullbackTensorTarget f F G)))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **Step 4 of the chain of Tag 03EL on a pure tensor.** Step 4 is the universal property of the
tensor product sheaf over `f⁻¹O_D`, traversed backwards, so the pairing it produces from a morphism
pairs two local sections by sending the sheafification-unit image of their tensor through that
morphism. -/
lemma pairingApp_pullbackTensorStep4_symm (V : X.Cᵒᵖ)
    (x : ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val.obj V)
    (s : ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val.obj V) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
          (pullbackTensorBottomHom f F G)).1 V x s =
      (pullbackTensorBottomHom f F G).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f)) (𝟙 _)).unit.app
            (((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val ⊗
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val)).app V
          (x ⊗ₜ[(ringPresheaf (inverseImageStructureCommRing f)).obj V] s)) :=
  pairingApp_bilinearEquivTensorSheafHom_symm (pullbackTensorBottomHom f F G) V x s

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **Steps 4, 5 and 6 of the chain of Tag 03EL on a pure tensor: the pairing at the bottom of the
chain pairs two local sections by the pure tensor of their images under the pullback unit.**

Precisely: the pairing `q₄` that steps 4, 5 and 6 produce from the identity carries a pair of local
sections `x` of `f⁻¹F` and `s` of `f⁻¹G` over `V` to the sheafification-unit image of
`η(x) ⊗ₜ η(s)`, where `η` is the unit of extension of scalars along `f^♯` — that is, to the pure
tensor of their images in `f^*F ⊗_{O_C} f^*G`. No scalar is left over.

This is the content of the bottom of the chain, and it is what the mathematics predicts: the
comparison of Tag 03EL is the morphism that sends a pure tensor to the pure tensor of the
pullbacks. It is `pairingApp_pullbackTensorStep4_symm` composed with
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul`,
the two steps being joined by `CategoryTheory.Adjunction.homEquiv_unit` for the adjunction of
Stacks 03CZ, which is what turns step 5 traversed backwards into "compose with the unit". -/
lemma pairingApp_pullbackTensorBottom (V : X.Cᵒᵖ)
    (x : ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val.obj V)
    (s : ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val.obj V) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
          (pullbackTensorBottomHom f F G)).1 V x s =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
            (𝟙 _)).unit.app
          (((extendScalarsFSharp f).obj
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val ⊗
            ((extendScalarsFSharp f).obj
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val)).app V
        ((((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val.app V x)
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.app V s)) := by
  refine Eq.trans (pairingApp_pullbackTensorStep4_symm f F G V x s) ?_
  have hb : pullbackTensorBottomHom f F G =
      (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          (inverseImageTensorSheaf f
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ≫
        (SheafOfModules.restrictScalars
            (commRingSheafMap X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).map
          ((pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
            (𝟙 (pullbackTensorTarget f F G))) :=
    (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv_unit _ _ _
  have h6 : (pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
      (𝟙 (pullbackTensorTarget f F G)) =
      (extendScalarsTensorIso (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom := by
    show (extendScalarsTensorIso (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom ≫
      𝟙 (pullbackTensorTarget f F G) = _
    exact Category.comp_id _
  rw [hb, h6]
  exact (CategoryTheory.comp_apply _ _ _).trans
    (extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) V x s)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Steps 2 and 3 of the chain of Tag 03EL on a pure tensor.** From a bilinear pairing `q` of the
inverse images, steps 3 and 2 produce a morphism `F ⊗_{O_D} G ⟶ f_*N`, and it carries the
sheafification-unit image of `a ⊗ₜ r` to the pair `(a, r)` pushed through the unit of `f⁻¹ ⊣ f_*`
and then through the direct image of `q` precomposed with the product comparison of `f⁻¹`.

The topos unit is where this stops, and it stops there for a reason rather than for want of a
lemma: `f⁻¹` has no description on sections for a `CategoryTheory.Sheaf.MorphismOfTopoi`, so the
pair of sections cannot be carried upstairs except through the unit. What *can* be removed is the
direct image, by `AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map`, once the
morphism of topoi is presented by a morphism of sites. -/
lemma pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (q : { q : moduleSheaf (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
          moduleSheaf (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
      IsBilinearPairing (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q })
    (U : Y.Cᵒᵖ) (a : F.val.obj U) (r : G.val.obj U) :
    ((pullbackTensorStep2 f F G N).symm ((pullbackTensorStep3 f F G N).symm q)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
              (𝟙 _)).unit.app
            (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.pushforward.map
            (prodComparison f.toToposHom.inverseImage
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫ q.1))
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.adj.unit.app
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
              moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))
          (Functor.prodObjMk a r)) :=
  (bilinearEquivTensorSheafHom_val_app_unit_tmul
      ((pullbackTensorStep3 f F G N).symm q) U a r).trans
    (pairingApp_inverseImageBilinearEquiv f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) q U a r)

end Chain

end Stacks.SheafOfModules

end
