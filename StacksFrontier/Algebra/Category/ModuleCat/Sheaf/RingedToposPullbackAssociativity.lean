module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTrilinearNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTrilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackRightUnitality
public import StacksCore.Tactic.StacksAttribute

/-!
# The associativity coherence of Tag 03EL

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The field
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity` asks that the
comparison `Stacks.SheafOfModules.pullbackTensorIso` of **Tag 03EL** be compatible with the
associator of the monoidal structure of Tag 01CA:

`f^*(α_{F,G,H}) ≫ δ_{F, G⊗H} ≫ (f^*F ◁ δ_{G,H}) =
δ_{F⊗G, H} ≫ (δ_{F,G} ▷ f^*H) ≫ α_{f^*F, f^*G, f^*H}`.

This file **proves that coherence**, at independent coefficient universes. Both sides are
morphisms of sheaves of `O_C`-modules out of `f^*((F ⊗ G) ⊗ H)`; the Yoneda step
`assocTrilinearEquiv` identifies such morphisms with the trilinear pairings of `f⁻¹F`, `f⁻¹G`
and `f⁻¹H` over `f⁻¹O_D`, and the two pairings the two sides produce are then computed on a
triple of local sections. Both are the iterated local pure tensor
`(1 ⊗ a) ⊗ ((1 ⊗ b) ⊗ (1 ⊗ c))` of the three units of Tag 03CZ.

## Main definitions

* `assocTrilinearEquiv`: **steps 1 to 3 of the three-variable chain of Tag 03EL.** Morphisms of
  sheaves of `O_C`-modules out of `f^*((F ⊗ G) ⊗ H)` are the trilinear pairings of `f⁻¹F`,
  `f⁻¹G` and `f⁻¹H` over `f⁻¹O_D` with values in `N` read over `f⁻¹O_D`. Its three factors are
  the adjunction of Tag 03D7, the three-variable universal property of the double tensor product
  sheaf `Stacks.SheafOfModules.trilinearEquivTensorSheafHom`, and the three-variable transport of
  Tag 03D3 `Stacks.SheafOfModules.inverseImageTrilinearEquiv`.
* `canonicalPairing`: the bilinear pairing `F ⨯ G ⟶ F ⊗ G` which the universal property of
  Tag 05NA carries to the identity; on local sections it is the local pure tensor.
* `invImageCanonicalPairing`: its inverse image, `f⁻¹F ⨯ f⁻¹G ⟶ f⁻¹(F ⊗ G)`, composed with the
  inverse product comparison of `f⁻¹`. It has no description on sections and is never evaluated.
* `invChainPairing`: steps 4 to 6 of the binary chain, inverted.

## Main results

* `associativity`: **the coherence**, character for character the field
  `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity`.
* `residual_associativity`: the hypothesis of `associativity_of_residual`, discharged.
* `associativity_of_residual`: **the coherence from one identity of triple pairings over
  `f⁻¹O_D`**, which is the Yoneda step on its own.
* `comparison_val_app_unit_canonicalPairing`: **the comparison of Tag 03EL on local sections.**
  `δ_{F,G}` carries the unit of Tag 03CZ of the canonical pairing of `a` and `b` to the local
  pure tensor of the two units, informally `δ(1 ⊗ (a ⊗ b)) = (1 ⊗ a) ⊗ (1 ⊗ b)`. This is the one
  statement about `δ` the coherence needs, and it is used three times — once per occurrence of
  the comparison in the two sides.
* `step123_eq`: **steps 1 to 3 of the binary chain on an arbitrary morphism out of `f^*(F ⊗ G)`**
  are the canonical pairing of the inverse images, the unit of Tag 03CZ and that morphism. The
  unit of Tag 03D3 cancels against the counit of the same adjunction, along which step 3
  transposes back, so nothing about a direct image on sections is needed; this is the mechanism
  of `Stacks.SheafOfModules.RingedToposPullback.step3_leftUnitor` with the unitor removed.
* `pairingApp_invChainPairing`: steps 4 to 6 inverted, on a pair of local sections. This is
  `step456_pairingApp` for an arbitrary morphism out of `f^*F ⊗ f^*G`.
* `pairingApp₃_trilinearEquivTensorSheafHom_symm`: the three-variable value formula for the
  universal property of the double tensor product sheaf, the companion of
  `Stacks.SheafOfModules.pairingApp_bilinearEquivTensorSheafHom_symm`.
* `trilinearEquivTensorSheafHom_symm_bilinearEquivTensorSheafHom` and
  `trilinearEquivTensorSheafHom_symm_associator_comp`: the triple pairing of a morphism out of
  `(F ⊗ G) ⊗ H` which factors through a bilinear pairing at either bracketing. These are where
  the associator of the tensor product sheaf enters, and it enters only through its value on
  local pure tensors.
* `assocTrilinearEquiv_comparison_left_comp` and
  `assocTrilinearEquiv_pullbackMap_comparison_comp`: **the two sides of the coherence, after the
  Yoneda step.** Each is a product comparison followed by the pairing which steps 4 to 6 produce
  from the second factor; neither carries a comparison of Tag 03EL any more, and
  `residual_pairing` is the identity between them.

## Implementation notes

**The decisive formula is `comparison_val_app_unit_canonicalPairing`, and the two sides of the
coherence meet because iterated units reassociate.** Neither `TensorProduct.smul_tmul` nor the
factoring of `ν` through `Stacks.Sheaves.RingedToposModules.baseChangeUnitor` is used, and no
unit comparison occurs anywhere in this file. The content is that `δ` carries the canonical
element `1 ⊗ (a ⊗ b)` of `f^*(F ⊗ G)` to `(1 ⊗ a) ⊗ (1 ⊗ b)`, which is the chain identity of
Tag 03EL read on a pair of local sections; applying it three times carries both sides to
`(1 ⊗ a) ⊗ ((1 ⊗ b) ⊗ (1 ⊗ c))`, the left-hand side needing no reassociation and the right-hand
side one application of the associator on local pure tensors.

**The three-variable chain stops at step 3 on purpose.** Steps 4, 5 and 6 of the three-variable
chain are exactly `Stacks.SheafOfModules.extendScalarsTrilinearEquiv`, and they are *bijections*,
so they contribute nothing to a Yoneda step that is only ever used through injectivity. In
particular **no value formula for `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso₃` is
needed, and none is proved here**: the two sides of the coherence are read through the *binary*
chain at the two splittings `(F ⊗ G, H)` and `(F, G ⊗ H)`, where the existing
`Stacks.SheafOfModules.RingedToposPullback.extendScalarsTensorIso_hom_val_app_unit_tmul` applies
unchanged. The ternary analogue would be needed by a proof which read both sides through the
three-variable chain; this one does not.

**The seams, and why every step is a term.** The computation crosses the two spellings
`Stacks.Sheaves.RingedToposModules.commRingSheaf J A hA` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA` of the sheaf of rings, and the
two spellings `(Tensor.ringSheaf Y.O).obj` and `TensorSheafification.structureRingPresheaf Y.O.obj`
of its underlying presheaf. The second pair agrees only at *default* transparency — it is a
`CategoryTheory.sheafCompose` which has to be unfolded — so a statement which names both is not
type-correct at `implicit` transparency and neither instance search nor `rw` will take the step.
Everything about the tensor product sheaf over a *fixed* sheaf of rings is therefore stated in
the section `Canonical` below, generically in a presheaf of commutative rings `A` and a sheaf
condition `hA` on its underlying presheaf of rings, where both spellings are variables; the
crossing to `Y.O` happens once per use, inside a `:=`, which is checked at default transparency.
For the same reason every step of a reduction below is a `congrArg`/`Eq.trans` chain rather than
a `rw`, and the reassociations are supplied by `reassoc₄` at objects which are all variables.

**Universes.** `X : RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}`: the two sites and
the two coefficient universes are independent, exactly as for
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`, and `associativity` is proved at
that generality. No unit comparison occurs in it — `ν : f^*O_D ≅ O_C` is what the two unitality
coherences have to read on sections, and nothing of the kind is needed here — so no step of the
reduction asks the two coefficient universes to be equal. Nothing assumes `Small` or
`EssentiallySmall`, identifies the two site universes, or inserts a universe-lifting
comparison.

**Spellings.** `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` is the local instance
under which `⊗`, `▷`, `◁` and `α_` mean what they mean in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal`; under it the monoidal
product is the tensor product sheaf on the nose, which is what lets
`Stacks.SheafOfModules.trilinearEquivTensorSheafHom` be applied to `(F ⊗ G) ⊗ H` without a
comparison. `Stacks.SheafOfModules.monoidalCategoryPresheafOfModules` is a local instance of the
section `Canonical`, where the objectwise tensor product of a tensor product sheaf with a
presheaf of modules occurs.

## What this file does not contain

**`PullbackCoherence` itself.** Only its `associativity` field is proved here. The other two are
`Stacks.SheafOfModules.RingedToposPullback.leftUnitality` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality` and
`Stacks.SheafOfModules.RingedToposPullback.rightUnitality` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackRightUnitality`, both at the
structure's own universes. All three fields therefore exist at the generality the structure is
stated at, and `PullbackCoherence f` is constructible from them; this file does not construct it,
and nothing here registers a `Monoidal` or `LaxMonoidal` instance.

**No naturality of `assocTrilinearEquiv` in the sheaf of values.** It is not needed: the two
sides are each a composite beginning with the comparison of Tag 03EL — after the pullback of the
associator has been moved to the `O_D` side by `assoc_pullbackMap_comp` — and such a composite is
handled by `step1_comparison_comp`, which is the chain identity of Tag 03EL at step 1.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace Stacks.SheafOfModules.RingedToposPullback

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-! ### Steps 1 to 3 of the three-variable chain -/

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the three-variable chain of Tag 03EL.** A morphism of sheaves of
`O_C`-modules out of `f^*((F ⊗ G) ⊗ H)` is the same thing as a trilinear pairing of `f⁻¹F`,
`f⁻¹G` and `f⁻¹H` over `f⁻¹O_D` with values in `N` read over `f⁻¹O_D`: transpose along the
adjunction of Tag 03D7, read the result as a triple pairing over `O_D` by the three-variable
universal property of the double tensor product sheaf, and transport it across `f⁻¹ ⊣ f_*`. -/
def assocTrilinearEquiv (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (f.pullbackModules.obj ((F ⊗ G) ⊗ H) ⟶ N) ≃
      { q : (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ⨯
            Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G)) ⨯
          Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj H) ⟶
            Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
        IsTrilinearPairing (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)) q } :=
  ((pullbackAdjPushforwardModules f).homEquiv ((F ⊗ G) ⊗ H) N).trans
    ((trilinearEquivTensorSheafHom (hA := (Tensor.ringSheaf Y.O).property)
        (F := F) (G := G) (H := H) (N := (pushforwardModules f).obj N)).symm.trans
      (inverseImageTrilinearEquiv f.toToposHom (Tensor.ringSheaf Y.O) F G H
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)).symm)

open Stacks.SheafOfModules in
/-- The adjunction of Tag 03D7 carries `f^*(α_{F,G,H}) ≫ u` to `α_{F,G,H}` followed by the
transpose of `u`. This is the one step of the left-hand side of the associativity coherence which
the chain discharges for free: it is the left-hand naturality of the adjunction, the associator
being a morphism of sheaves of `O_D`-modules. -/
theorem assoc_pullbackMap_comp (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (u : f.pullbackModules.obj (F ⊗ (G ⊗ H)) ⟶ N) :
    (pullbackAdjPushforwardModules f).homEquiv ((F ⊗ G) ⊗ H) N
        (f.pullbackModules.map (α_ F G H).hom ≫ u) =
      (α_ F G H).hom ≫
        (pullbackAdjPushforwardModules f).homEquiv (F ⊗ (G ⊗ H)) N u :=
  (pullbackAdjPushforwardModules f).homEquiv_naturality_left (α_ F G H).hom u

/-! ### The coherence from one identity of triple pairings -/

open Stacks.SheafOfModules in
/-- **The associativity coherence of Tag 03EL, from one identity of triple pairings over
`f⁻¹O_D`.** The conclusion is the statement of
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity` verbatim. The
hypothesis is the identity the Yoneda step leaves: the two triple pairings of `f⁻¹F`, `f⁻¹G` and
`f⁻¹H` over `f⁻¹O_D` produced by the two sides agree. Nothing else about the comparison of
Tag 03EL is used — only that steps 1 to 3 of the three-variable chain are a bijection. -/
theorem associativity_of_residual (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (h : assocTrilinearEquiv f F G H
          (f.pullbackModules.obj F ⊗
            (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
          (f.pullbackModules.map (α_ F G H).hom ≫ pullbackTensorComparison f F (G ⊗ H) ≫
            (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H)) =
        assocTrilinearEquiv f F G H
          (f.pullbackModules.obj F ⊗
            (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
          (pullbackTensorComparison f (F ⊗ G) H ≫
            (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
              (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
                (f.pullbackModules.obj H)).hom)) :
    f.pullbackModules.map (α_ F G H).hom ≫ pullbackTensorComparison f F (G ⊗ H) ≫
        (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H) =
      pullbackTensorComparison f (F ⊗ G) H ≫
        (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
          (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
            (f.pullbackModules.obj H)).hom :=
  (assocTrilinearEquiv f F G H
    (f.pullbackModules.obj F ⊗
      (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))).injective h


/-! ### The canonical pairings into a tensor product sheaf

The statements of this section are about the tensor product sheaf of Tag 05NA over a presheaf of
commutative rings `A` whose underlying presheaf of rings is a sheaf, and mention no morphism of
topoi. They are the three-variable companions of
`Stacks.SheafOfModules.pairingApp_bilinearEquivTensorSheafHom_symm`. -/

section Canonical

open Stacks.SheafOfModules Stacks.PresheafOfModules.ChangeOfRings

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} (hA : Presheaf.IsSheaf J (ringPresheaf A))
  (F G H : _root_.SheafOfModules.{w} (commRingSheaf J A hA))

/-- **The canonical bilinear pairing of two sheaves of modules into their tensor product
sheaf**: the pairing the universal property of Tag 05NA carries to the identity. On a pair of
local sections it is the local pure tensor. -/
def canonicalPairing :
    Sheaf.moduleSheaf (commRingSheaf J A hA) F ⨯ Sheaf.moduleSheaf (commRingSheaf J A hA) G ⟶
      Sheaf.moduleSheaf (commRingSheaf J A hA)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
            F).obj G) :=
  ((bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G)
    (N := ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
        F).obj G)).symm (𝟙 _)).1

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The canonical bilinear pairing on a pair of local sections is the local pure tensor.** -/
theorem pairingApp_canonicalPairing (U : Cᵒᵖ) (a : F.val.obj U) (b : G.val.obj U) :
    pairingApp (commRingSheaf J A hA) (canonicalPairing hA F G) U a b =
      ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A hA) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app U
        (a ⊗ₜ[(A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) :=
  pairingApp_bilinearEquivTensorSheafHom_symm (hA := hA)
    (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
        F).obj G)) U a b

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)]
  [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The comparison of Tag 05NA identifying the sheafification of the double objectwise tensor
product with the double tensor product sheaf, on the sheafification unit of a pure tensor whose
left factor is itself a pure tensor: it inserts the inner sheafification unit. -/
theorem sheafifyDoubleTensorIso_hom_val_app_unit_tmul (U : Cᵒᵖ)
    (a : F.val.obj U) (b : G.val.obj U) (c : H.val.obj U) :
    (sheafifyDoubleTensorIso (hA := hA) (F := F) (G := G) (H := H)).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A hA) (𝟙 _)).unit.app ((F.val ⊗ G.val) ⊗ H.val)).app U
          ((a ⊗ₜ[(A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A hA) (𝟙 _)).unit.app
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
                  F).obj G).val ⊗ H.val)).app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A hA) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
          (a ⊗ₜ[(A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c) :=
  sheafificationUnit_naturality_app (A₂ := A) hA
    (TensorSheafification.toSheafify A hA (F.val ⊗ G.val) ▷ H.val) U _

variable (N : _root_.SheafOfModules.{w} (commRingSheaf J A hA))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)]
  [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- Morphisms out of the double tensor product sheaf, read as morphisms of presheaves of modules
out of the double objectwise tensor product: the comparison of Tag 05NA followed by the
sheafification unit. -/
theorem doubleTensorSheafHomEquivPresheafTensorHom_eq
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
              F).obj G)).obj H ⟶ N) :
    doubleTensorSheafHomEquivPresheafTensorHom (hA := hA) t =
      (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A hA) (𝟙 _)).unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
        ((sheafifyDoubleTensorIso (hA := hA) (F := F) (G := G) (H := H)).hom ≫ t).val :=
  (congrArg ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A hA) (𝟙 _)).homEquiv ((F.val ⊗ G.val) ⊗ H.val) N)
      (congrArg (fun z ↦ (sheafifyDoubleTensorIso (hA := hA)
          (F := F) (G := G) (H := H)).hom ≫ z) (Category.comp_id t))).trans
    ((PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A hA) (𝟙 _)).homEquiv_unit _ _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The triple pairing recovered from a morphism out of the double tensor product sheaf, on a
triple of local sections.** It carries `(a, b, c)` to the image of the local pure tensor of the
local pure tensor of `a` and `b` with `c`. This is the three-variable form of
`Stacks.SheafOfModules.pairingApp_bilinearEquivTensorSheafHom_symm`, and the value formula for
the direction of `Stacks.SheafOfModules.trilinearEquivTensorSheafHom` which the Yoneda step of
the associativity coherence traverses backwards. -/
theorem pairingApp₃_trilinearEquivTensorSheafHom_symm
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
              F).obj G)).obj H ⟶ N) (U : Cᵒᵖ)
    (a : F.val.obj U) (b : G.val.obj U) (c : H.val.obj U) :
    pairingApp₃ (commRingSheaf J A hA)
        ((trilinearEquivTensorSheafHom (hA := hA)
          (F := F) (G := G) (H := H) (N := N)).symm t).1 U a b c =
      t.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A hA) (𝟙 _)).unit.app
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A
                    (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G).val ⊗ H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A hA) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
            (a ⊗ₜ[(A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c)) :=
  (pairingApp₃_pairingOfTensorHom₃
        (doubleTensorSheafHomEquivPresheafTensorHom (hA := hA) t) U a b c).trans
    ((CategoryTheory.congr_fun
          (congrArg (fun m ↦ PresheafOfModules.Hom.app m U)
            (doubleTensorSheafHomEquivPresheafTensorHom_eq hA F G H N t))
          ((a ⊗ₜ[(A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c)).trans
      ((CategoryTheory.comp_apply _ _ _).trans
        (congrArg (fun z ↦ t.val.app U z)
          (sheafifyDoubleTensorIso_hom_val_app_unit_tmul hA F G H U a b c))))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)] in
/-- A triple pairing which bundles its first two arguments by a pairing `p` and then pairs the
result with the third by `q`, on a triple of local sections. -/
theorem pairingApp₃_prodMap_comp {R : Sheaf J RingCat.{w}}
    {P Q S T M : _root_.SheafOfModules.{w} R}
    (p : Sheaf.moduleSheaf R P ⨯ Sheaf.moduleSheaf R Q ⟶ Sheaf.moduleSheaf R S)
    (q : Sheaf.moduleSheaf R S ⨯ Sheaf.moduleSheaf R T ⟶ Sheaf.moduleSheaf R M) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R P))
    (b : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R Q))
    (c : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R T)) :
    pairingApp₃ R (prod.map p (𝟙 (Sheaf.moduleSheaf R T)) ≫ q) U a b c =
      pairingApp R q U (pairingApp R p U a b) c := by
  simp only [pairingApp₃, pairingApp, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk, CategoryTheory.Functor.map_id,
    types_id_apply]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)] in
/-- A triple pairing which bundles its last two arguments by a pairing `p` and then pairs the
first with the result by `q`, on a triple of local sections. -/
theorem pairingApp₃_lift_comp {R : Sheaf J RingCat.{w}}
    {P Q S T M : _root_.SheafOfModules.{w} R}
    (p : Sheaf.moduleSheaf R Q ⨯ Sheaf.moduleSheaf R T ⟶ Sheaf.moduleSheaf R S)
    (q : Sheaf.moduleSheaf R P ⨯ Sheaf.moduleSheaf R S ⟶ Sheaf.moduleSheaf R M) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R P))
    (b : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R Q))
    (c : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R T)) :
    pairingApp₃ R (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ p) ≫ q) U a b c =
      pairingApp R q U a (pairingApp R p U b c) := by
  simp only [pairingApp₃, pairingApp, Functor.map_comp_apply, Functor.map_lift_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The triple pairing of the morphism out of `(F ⊗ G) ⊗ H` determined by a bilinear pairing
of `F ⊗ G` and `H`**: it bundles its first two arguments into the canonical pairing and then
pairs. -/
theorem trilinearEquivTensorSheafHom_symm_bilinearEquivTensorSheafHom
    (w : { q : Sheaf.moduleSheaf (commRingSheaf J A hA)
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
              F).obj G) ⨯
        Sheaf.moduleSheaf (commRingSheaf J A hA) H ⟶
          Sheaf.moduleSheaf (commRingSheaf J A hA) N //
      IsBilinearPairing (commRingSheaf J A hA) q }) :
    ((trilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (H := H) (N := N)).symm
        (bilinearEquivTensorSheafHom (hA := hA) w)).1 =
      prod.map (canonicalPairing hA F G) (𝟙 (Sheaf.moduleSheaf (commRingSheaf J A hA) H)) ≫
        w.1 :=
  pairing₃_ext (commRingSheaf J A hA) fun U a b c ↦
    (pairingApp₃_trilinearEquivTensorSheafHom_symm hA F G H N
          (bilinearEquivTensorSheafHom (hA := hA) w) U a b c).trans
      ((bilinearEquivTensorSheafHom_val_app_unit_tmul (hA := hA) w U _ c).trans
        ((congrArg (fun z ↦ pairingApp (commRingSheaf J A hA) w.1 U z c)
            (pairingApp_canonicalPairing hA F G U a b)).symm.trans
          (pairingApp₃_prodMap_comp (canonicalPairing hA F G) w.1 U a b c).symm))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The triple pairing of the associativity constraint of Tag 05NA followed by the morphism
out of `F ⊗ (G ⊗ H)` determined by a bilinear pairing of `F` and `G ⊗ H`**: it bundles its last
two arguments into the canonical pairing and then pairs. This is the one place the associativity
coherence of Tag 03EL uses the associator of the tensor product sheaf, and it uses it only
through its value on local pure tensors. -/
theorem trilinearEquivTensorSheafHom_symm_associator_comp
    (w : { q : Sheaf.moduleSheaf (commRingSheaf J A hA) F ⨯
          Sheaf.moduleSheaf (commRingSheaf J A hA)
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
                G).obj H) ⟶
          Sheaf.moduleSheaf (commRingSheaf J A hA) N //
      IsBilinearPairing (commRingSheaf J A hA) q }) :
    ((trilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (H := H) (N := N)).symm
        ((tensorSheafAssociator A hA F G H).hom ≫
          bilinearEquivTensorSheafHom (hA := hA) w)).1 =
      prod.lift (prod.fst ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ canonicalPairing hA G H) ≫ w.1 :=
  pairing₃_ext (commRingSheaf J A hA) fun U a b c ↦
    (pairingApp₃_trilinearEquivTensorSheafHom_symm hA F G H N
          ((tensorSheafAssociator A hA F G H).hom ≫
            bilinearEquivTensorSheafHom (hA := hA) w) U a b c).trans
      ((comp_val_app_apply (tensorSheafAssociator A hA F G H).hom
            (bilinearEquivTensorSheafHom (hA := hA) w) U _).trans
        ((congrArg (fun z ↦ (bilinearEquivTensorSheafHom (hA := hA) w).val.app U z)
              (tensorSheafAssociator_hom_val_app_tmul A hA F G H U a b c)).trans
          ((bilinearEquivTensorSheafHom_val_app_unit_tmul (hA := hA) w U a _).trans
            ((congrArg (fun z ↦ pairingApp (commRingSheaf J A hA) w.1 U a z)
                (pairingApp_canonicalPairing hA G H U b c)).symm.trans
              (pairingApp₃_lift_comp (canonicalPairing hA G H) w.1 U a b c).symm))))

end Canonical

/-! ### The binary chain at the two splittings, and the coherence -/

section Coherence

open Stacks.SheafOfModules Stacks.PresheafOfModules.ChangeOfRings

/-- **Steps 4 to 6 of the chain of Tag 03EL, inverted**: the pairing of `f⁻¹F` and `f⁻¹G` over
`f⁻¹O_D` which a morphism of sheaves of `O_C`-modules out of `f^*F ⊗ f^*G` produces. -/
def invChainPairing (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj G ⟶ N) :=
  (pullbackTensorStep4 f F G N).symm ((pullbackTensorStep5 f F G N).symm
    ((pullbackTensorStep6 f F G N).symm k))

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Steps 4 to 6 of the chain of Tag 03EL, inverted, on a pair of local sections.** The pairing
carries `(a, b)` to the image under the given morphism of the local pure tensor of the two units
of Tag 03CZ: informally `(a, b) ↦ k((1 ⊗ a) ⊗ (1 ⊗ b))`. This is
`Stacks.SheafOfModules.RingedToposPullback.step456_pairingApp` for an arbitrary morphism out of
the tensor product of the pullbacks, and at **independent** coefficient universes: the unit
comparison `ν`, which is what ties the two universes together, does not occur. -/
theorem pairingApp_invChainPairing (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj G ⟶ N) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G))) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        (invChainPairing f F G N k).1 U a b =
      k.val.app U
        ((TensorSheafification.toSheafify X.O.obj (Tensor.ringSheaf X.O).property
            ((f.pullbackModules.obj F).val ⊗ (f.pullbackModules.obj G).val)).app U
          (((structureAdjunction f).unit.app
                ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U a ⊗ₜ
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G)).val.app U b)) :=
  (pairingApp_bilinearEquivTensorSheafHom_symm
        (hA := isSheaf_inverseImageStructureCommRing f) _ U a b).trans
    ((congrArg (fun m : inverseImageTensorSheaf f
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G) ⟶
          (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N ↦ m.val.app U _)
          ((structureAdjunction f).homEquiv_unit _ _ _)).trans
      (congrArg (fun z ↦ k.val.app U z)
        (extendScalarsTensorIso_hom_val_app_unit_tmul (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)).property
          (Tensor.ringSheaf X.O).property
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G) U a b)))

open Stacks.SheafOfModules in
/-! #### The comparison of Tag 03EL on local sections -/

/-- **The chain identity at step 1**: the first step of the chain of Tag 03EL carries a composite
beginning with the comparison to the image of its second factor under the inverses of steps 2 to
6. This is `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp` with the first step
of the chain performed. -/
theorem step1_comparison_comp (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj G ⟶ N) :
    pullbackTensorStep1 f F G N (pullbackTensorComparison f F G ≫ k) =
      (pullbackTensorStep2 f F G N).symm
        ((pullbackTensorStep3 f F G N).symm (invChainPairing f F G N k)) :=
  (congrArg (pullbackTensorStep1 f F G N)
      (Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp f F G k)).trans
    ((pullbackTensorStep1 f F G N).apply_symm_apply _)

/-- **The canonical pairing of two inverse images into the inverse image of the tensor product
sheaf**: the inverse product comparison of `f⁻¹`, which is an isomorphism because `f⁻¹` is left
exact, followed by the inverse image of the canonical pairing over `O_D`. It has no description
on sections — `f⁻¹` has none — and it is never evaluated below: it occurs only as the first
factor of the pairing which steps 1 to 3 of the chain produce. -/
def invImageCanonicalPairing (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ⨯
        Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) :=
  (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)).inv ≫
    f.toToposHom.inverseImage.map (canonicalPairing (Tensor.ringSheaf Y.O).property F G)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The product comparison of `f⁻¹` followed by the canonical pairing of the inverse images is
the inverse image of the canonical pairing. This is the hypothesis in the form the iterated
product comparisons of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTrilinear` take it. -/
theorem prodComparison_comp_invImageCanonicalPairing
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    prodComparison f.toToposHom.inverseImage (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G) ≫
        invImageCanonicalPairing f F G =
      f.toToposHom.inverseImage.map (canonicalPairing (Tensor.ringSheaf Y.O).property F G) :=
  (congrArg (fun z ↦ z ≫ (PreservesLimitPair.iso f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)).inv ≫
        f.toToposHom.inverseImage.map (canonicalPairing (Tensor.ringSheaf Y.O).property F G))
      (PreservesLimitPair.iso_hom f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)).symm).trans
    (Iso.hom_inv_id_assoc _ _)

/-- Cancelling a unit against a counit: the transpose of a transpose. -/
private alias adjUnitCounitCancel := adj_unit_counit_cancel

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on an arbitrary morphism out of `f^*(F ⊗ G)`.** The
pairing of `f⁻¹F` and `f⁻¹G` over `f⁻¹O_D` they produce is the canonical pairing into
`f⁻¹(F ⊗ G)`, followed by the unit of Tag 03CZ, followed by the given morphism: informally
`(a, b) ↦ v(1 ⊗ (a ⊗ b))`.

The unit of Tag 03D3 cancels against the counit of the same adjunction, along which step 3
transposes back, so nothing about a direct image on sections is needed; this is the mechanism of
`Stacks.SheafOfModules.RingedToposPullback.step3_leftUnitor`, with the left unitor replaced by the
identity and the morphism out of the pullback left arbitrary. -/
theorem step123_eq (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (v : f.pullbackModules.obj (F ⊗ G) ⟶ N) :
    (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
        (pullbackTensorStep1 f F G N v))).1 =
      invImageCanonicalPairing f F G ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) ≫
            (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map v) := by
  have hstep2 : (pullbackTensorStep2 f F G (f.pullbackModules.obj (F ⊗ G))
        ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G))).1 =
      canonicalPairing (Tensor.ringSheaf Y.O).property F G ≫
        (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G)) :=
    congrArg Subtype.val
      ((congrArg (fun z ↦ pullbackTensorStep2 f F G (f.pullbackModules.obj (F ⊗ G)) z)
          (Category.id_comp ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G))).symm).trans
        (bilinearEquivTensorSheafHom_symm_naturality (hA := (Tensor.ringSheaf Y.O).property)
          (𝟙 _) ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G))))
  have hz : (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G)) ≫
        (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pushforwardModules f).map v) =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) (F ⊗ G)) ≫
        f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
                ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) ≫
              (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map v)) :=
    ((congrArg₂ (fun p q ↦ p ≫ q) (moduleSheafFunctor_map_pullbackUnit f (F ⊗ G))
            (moduleSheafFunctor_map_directImageModules_map f.toToposHom (Tensor.ringSheaf Y.O)
              ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map v))).trans
        (Category.assoc _ _ _)).trans
      (congrArg (fun z ↦ f.toToposHom.adj.unit.app
            (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) (F ⊗ G)) ≫ z)
        ((f.toToposHom.pushforward.map_comp _ _).symm.trans
          (congrArg f.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map_comp _ _).symm)))
  refine Eq.trans (congrArg (fun z ↦ (pullbackTensorStep3 f F G N
      (pullbackTensorStep2 f F G N z)).1)
    ((pullbackAdjPushforwardModules f).homEquiv_unit (F ⊗ G) N v)) ?_
  refine Eq.trans (congrArg (fun p ↦ (pullbackTensorStep3 f F G N p).1)
    (pullbackTensorStep2_naturality f F G
      ((pullbackAdjPushforwardModules f).unit.app (F ⊗ G)) v)) ?_
  refine Eq.trans (inverseImageBilinearEquiv_symm_apply_coe_eq_comp_counit f.toToposHom
    (Tensor.ringSheaf Y.O) F G
    ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) _) ?_
  refine Eq.trans (congrArg (fun m ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)).inv ≫
      f.toToposHom.inverseImage.map m ≫ f.toToposHom.adj.counit.app _)
    (((congrArg (fun z ↦ z ≫ (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
              ((pushforwardModules f).map v)) hstep2).trans
        (Category.assoc _ _ _)).trans
      (congrArg (fun z ↦ canonicalPairing (Tensor.ringSheaf Y.O).property F G ≫ z) hz))) ?_
  refine Eq.trans (congrArg (fun z ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)).inv ≫ z ≫
      f.toToposHom.adj.counit.app _)
    (f.toToposHom.inverseImage.map_comp _ _)) ?_
  exact (reassoc₄ _ _ _ _).trans
    (congrArg (fun z ↦ invImageCanonicalPairing f F G ≫ z)
      (adjUnitCounitCancel f.toToposHom.adj _))

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] [X.J.HasSheafCompose (forget RingCat)]
  [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The identity acts as the identity on a local section. -/
private lemma idValAppApply {R : Sheaf X.J RingCat.{w}} (M : _root_.SheafOfModules.{w} R)
    (U : X.Cᵒᵖ) (x : M.val.obj U) : (𝟙 M : M ⟶ M).val.app U x = x :=
  rfl

open Stacks.SheafOfModules in
/-- **The comparison of Tag 03EL on the unit of Tag 03CZ of a canonical pairing.** This is the
section formula the associativity coherence needs of `δ`: the comparison carries the image under
the unit of Tag 03CZ of the canonical pairing of `a` and `b` to the local pure tensor of the two
units, informally `δ(1 ⊗ (a ⊗ b)) = (1 ⊗ a) ⊗ (1 ⊗ b)`.

It is the chain identity of Tag 03EL read on a pair of local sections: steps 1 to 3 carry the
comparison to the canonical pairing followed by the unit followed by the comparison
(`step123_eq`), and the inverses of steps 4 to 6 carry the identity to the local pure tensor of
the two units (`pairingApp_invChainPairing`). -/
theorem comparison_val_app_unit_canonicalPairing
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G))) :
    (pullbackTensorComparison f F G).val.app U
        (((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G))).val.app U
          (pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            (invImageCanonicalPairing f F G) U a b)) =
      (TensorSheafification.toSheafify X.O.obj (Tensor.ringSheaf X.O).property
          ((f.pullbackModules.obj F).val ⊗ (f.pullbackModules.obj G).val)).app U
        (((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U a ⊗ₜ
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj G)).val.app U b) := by
  have hchain := congrArg Subtype.val
    ((congrArg (pullbackTensorStep3 f F G
          (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G))
        ((congrArg (pullbackTensorStep2 f F G
              (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G))
            (((congrArg (pullbackTensorStep1 f F G
                  (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G))
                (Category.comp_id (pullbackTensorComparison f F G)).symm).trans
              (step1_comparison_comp f F G
                (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G) (𝟙 _))))).trans
          ((pullbackTensorStep2 f F G
            (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G)).apply_symm_apply _))).trans
      ((pullbackTensorStep3 f F G
        (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G)).apply_symm_apply _))
  refine Eq.trans ?_ (Eq.trans (congrArg (fun p ↦
      pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)) p U a b) hchain)
    ((pairingApp_invChainPairing f F G
        (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G) (𝟙 _) U a b).trans
      (idValAppApply (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G) U _)))
  refine Eq.trans ?_ (congrArg (fun p ↦
      pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)) p U a b)
    (step123_eq f F G (f.pullbackModules.obj F ⊗ f.pullbackModules.obj G)
      (pullbackTensorComparison f F G)).symm)
  exact (comp_val_app_apply ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)))
        ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map
          (pullbackTensorComparison f F G)) U _).symm.trans
    (pairingApp_comp (invImageCanonicalPairing f F G)
      ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) ≫
        (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map
          (pullbackTensorComparison f F G)) U a b).symm

/-! #### The two sides of the coherence after the Yoneda step -/

/-- Keeping the first of three factors and bundling the last two by an operation, read through
the iterated product comparison. This is the companion of
`Stacks.SheafOfModules.prodComparison₃_comp_prodMap` for the other bracketing, with the
reassociation of the triple product folded into the `prod.lift`. -/
theorem prodComparison₃_comp_liftFstLift {E : Type u} [Category.{v} E] {E' : Type u'}
    [Category.{v'} E'] [HasFiniteProducts E] [HasFiniteProducts E'] {Φ : E' ⥤ E}
    [PreservesFiniteProducts Φ] {P Q S S' : E'} (opO : Q ⨯ S ⟶ S')
    (opΦ : Φ.obj Q ⨯ Φ.obj S ⟶ Φ.obj S')
    (hop : prodComparison Φ Q S ≫ opΦ = Φ.map opO) :
    prodComparison₃ Φ P Q S ≫ prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ opΦ) =
      Φ.map (prod.lift (prod.fst ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ opO)) ≫
        prodComparison Φ P S' := by
  refine prod.hom_ext ?_ ?_
  · simp [prodComparison₃, ← Functor.map_comp]
  · rw [Category.assoc, prod.lift_snd, Category.assoc, prodComparison_snd,
      ← Functor.map_comp, prod.lift_snd, ← Category.assoc,
      prodComparison₃_comp_liftFstSnd, Category.assoc, hop, ← Functor.map_comp]

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the three-variable chain, written out**: the inverse of the iterated
product comparison, the inverse image of the triple pairing over `O_D`, and the counit of the
adjunction of topoi. -/
theorem assocTrilinearEquiv_apply_coe (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (u : f.pullbackModules.obj ((F ⊗ G) ⊗ H) ⟶ N) :
    (assocTrilinearEquiv f F G H N u).1 =
      inv (prodComparison₃ f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H)) ≫
        f.toToposHom.inverseImage.map
            ((trilinearEquivTensorSheafHom (hA := (Tensor.ringSheaf Y.O).property)
              (F := F) (G := G) (H := H) (N := (pushforwardModules f).obj N)).symm
                (pullbackTensorStep1 f (F ⊗ G) H N u)).1 ≫
          f.toToposHom.adj.counit.app
            (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
              ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)) :=
  congrArg (fun m ↦ inv (prodComparison₃ f.toToposHom.inverseImage
      (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
      (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)
      (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H)) ≫ m)
    (f.toToposHom.adj.homEquiv_counit _ _ _)

/-- Cancelling a unit against a counit, after an isomorphism `c` has been moved across `m`: the
inverse of `c`, the image of `m` followed by the transpose of `pc ≫ q`, and the counit give `Φ' ≫ q`
whenever `c ≫ Φ' = Φ.map m ≫ pc`. -/
private theorem inv_comp_map_unit_comp_counit {E : Type*} [Category E] {D : Type*} [Category D]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) {A B : D} {A' B' M : E} (c : L.obj A ⟶ A') [IsIso c]
    (m : A ⟶ B) (pc : L.obj B ⟶ B') (Φ' : A' ⟶ B') (q : B' ⟶ M)
    (h : c ≫ Φ' = L.map m ≫ pc) :
    inv c ≫ L.map (m ≫ adj.unit.app B ≫ R.map (pc ≫ q)) ≫ adj.counit.app M = Φ' ≫ q := by
  rw [Functor.map_comp, Category.assoc, adjUnitCounitCancel, ← reassoc_of% h,
    IsIso.inv_hom_id_assoc]

/-- Steps 1 to 3 of the three-variable chain, once the first step has been read as a morphism
`m` followed by the bijection of Tag 03D3 of a pairing `q` of `f⁻¹P` and `f⁻¹Q`: the result is the
pairing `q` precomposed with any `Φ'` which agrees with `m` through the product comparisons. -/
private theorem assocTrilinearEquiv_coe_of_step1
    (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (u : f.pullbackModules.obj ((F ⊗ G) ⊗ H) ⟶ N)
    (P Q : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (m : (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F ⨯ Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G) ⨯
        Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H ⟶
      Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) P ⨯ Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) Q)
    (q : { q : Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj P) ⨯
          Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj Q) ⟶
          Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
        IsBilinearPairing (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)) q })
    (Φ' : (f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F) ⨯
          f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)) ⨯
        f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H) ⟶
      f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) P) ⨯
        f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) Q))
    (h : prodComparison₃ f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H) ≫ Φ' =
        f.toToposHom.inverseImage.map m ≫ prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) P) (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) Q))
    (hz : ((trilinearEquivTensorSheafHom (hA := (Tensor.ringSheaf Y.O).property)
            (F := F) (G := G) (H := H) (N := (pushforwardModules f).obj N)).symm
              (pullbackTensorStep1 f (F ⊗ G) H N u)).1 =
        m ≫ (inverseImageBilinearEquiv f.toToposHom (Tensor.ringSheaf Y.O) P Q
          ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) q).1) :
    (assocTrilinearEquiv f F G H N u).1 = Φ' ≫ q.1 :=
  (assocTrilinearEquiv_apply_coe f F G H N u).trans
    ((congrArg (fun z ↦ inv (prodComparison₃ f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H)) ≫
        f.toToposHom.inverseImage.map z ≫ f.toToposHom.adj.counit.app _)
      (hz.trans (congrArg (fun z ↦ m ≫ z)
        (inverseImageBilinearEquiv_apply_coe_eq_unit_comp f.toToposHom (Tensor.ringSheaf Y.O)
          P Q ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) q)))).trans
      (inv_comp_map_unit_comp_counit f.toToposHom.adj _ m _ Φ' q.1 h))

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the three-variable chain on the right-hand side of the associativity
coherence.** The triple pairing produced by a composite beginning with the comparison of
Tag 03EL at the splitting `(F ⊗ G, H)` bundles its first two arguments into the canonical
pairing of the inverse images and then applies the pairing which steps 4 to 6 produce from the
second factor. The comparison is gone. -/
theorem assocTrilinearEquiv_comparison_left_comp
    (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj (F ⊗ G) ⊗ f.pullbackModules.obj H ⟶ N) :
    (assocTrilinearEquiv f F G H N (pullbackTensorComparison f (F ⊗ G) H ≫ k)).1 =
      prod.map (invImageCanonicalPairing f F G)
          (𝟙 (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj H))) ≫
        (invChainPairing f (F ⊗ G) H N k).1 :=
  assocTrilinearEquiv_coe_of_step1 f F G H N _ (F ⊗ G) H
    (prod.map (canonicalPairing (Tensor.ringSheaf Y.O).property F G)
      (𝟙 (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) H)))
    (invChainPairing f (F ⊗ G) H N k)
    (prod.map (invImageCanonicalPairing f F G)
      (𝟙 (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj H))))
    (prodComparison₃_comp_prodMap (canonicalPairing (Tensor.ringSheaf Y.O).property F G)
      (invImageCanonicalPairing f F G) (prodComparison_comp_invImageCanonicalPairing f F G))
    ((congrArg (fun z ↦ ((trilinearEquivTensorSheafHom (hA := (Tensor.ringSheaf Y.O).property)
          (F := F) (G := G) (H := H) (N := (pushforwardModules f).obj N)).symm z).1)
        (step1_comparison_comp f (F ⊗ G) H N k)).trans
      (trilinearEquivTensorSheafHom_symm_bilinearEquivTensorSheafHom
        (Tensor.ringSheaf Y.O).property F G H ((pushforwardModules f).obj N) _))

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the three-variable chain on the left-hand side of the associativity
coherence.** The triple pairing produced by the pullback of the associator followed by a
composite beginning with the comparison of Tag 03EL at the splitting `(F, G ⊗ H)` bundles its
last two arguments into the canonical pairing of the inverse images and then applies the pairing
which steps 4 to 6 produce from the second factor. The associator is discharged twice: once by
the left-hand naturality of the adjunction of Tag 03D7 (`assoc_pullbackMap_comp`), which moves it
to the `O_D` side, and once by its value on local pure tensors. -/
theorem assocTrilinearEquiv_pullbackMap_comparison_comp
    (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj (G ⊗ H) ⟶ N) :
    (assocTrilinearEquiv f F G H N (f.pullbackModules.map (α_ F G H).hom ≫
        pullbackTensorComparison f F (G ⊗ H) ≫ k)).1 =
      prod.lift (prod.fst ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ invImageCanonicalPairing f G H) ≫
        (invChainPairing f F (G ⊗ H) N k).1 :=
  assocTrilinearEquiv_coe_of_step1 f F G H N _ F (G ⊗ H)
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫
        canonicalPairing (Tensor.ringSheaf Y.O).property G H))
    (invChainPairing f F (G ⊗ H) N k)
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ invImageCanonicalPairing f G H))
    (prodComparison₃_comp_liftFstLift (canonicalPairing (Tensor.ringSheaf Y.O).property G H)
      (invImageCanonicalPairing f G H) (prodComparison_comp_invImageCanonicalPairing f G H))
    ((congrArg (fun z ↦ ((trilinearEquivTensorSheafHom (hA := (Tensor.ringSheaf Y.O).property)
          (F := F) (G := G) (H := H) (N := (pushforwardModules f).obj N)).symm z).1)
        ((assoc_pullbackMap_comp f F G H N (pullbackTensorComparison f F (G ⊗ H) ≫ k)).trans
          ((congrArg (fun z ↦ (α_ F G H).hom ≫ z)
              (step1_comparison_comp f F (G ⊗ H) N k)).trans
            (congrArg (fun z ↦ z ≫ (pullbackTensorStep2 f F (G ⊗ H) N).symm
                ((pullbackTensorStep3 f F (G ⊗ H) N).symm (invChainPairing f F (G ⊗ H) N k)))
              (congrArg Iso.hom (associator_eq_tensorSheafAssociator Y.O.obj
                (Tensor.ringSheaf Y.O).property F G H)))))).trans
      (trilinearEquivTensorSheafHom_symm_associator_comp (Tensor.ringSheaf Y.O).property F G H
        ((pushforwardModules f).obj N) _))

/-! ### The residual, discharged -/

open Stacks.SheafOfModules in
/-- **The identity of triple pairings over `f⁻¹O_D` which the associativity coherence of
Tag 03EL comes down to.** Both sides carry a triple `(a, b, c)` of local sections to the iterated
local pure tensor `(1 ⊗ a) ⊗ ((1 ⊗ b) ⊗ (1 ⊗ c))` of the three units of Tag 03CZ: on the left the
inner comparison acts in the second factor and nothing has to be reassociated, on the right the
inner comparison acts in the first factor and the associator of Tag 01CA reassociates the result,
which it does by its value on local pure tensors. -/
theorem residual_pairing (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    prod.lift (prod.fst ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ invImageCanonicalPairing f G H) ≫
        (invChainPairing f F (G ⊗ H)
          (f.pullbackModules.obj F ⊗
            (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
          (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H)).1 =
      prod.map (invImageCanonicalPairing f F G)
          (𝟙 (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj H))) ≫
        (invChainPairing f (F ⊗ G) H
          (f.pullbackModules.obj F ⊗
            (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
          ((pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
            (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
              (f.pullbackModules.obj H)).hom)).1 := by
  refine pairing₃_ext (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
    fun U a b c ↦ ?_
  refine Eq.trans (pairingApp₃_lift_comp (invImageCanonicalPairing f G H) _ U a b c) ?_
  refine Eq.trans (pairingApp_invChainPairing f F (G ⊗ H) _
    (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H) U a _) ?_
  refine Eq.trans (whiskerLeft_val_app_toSheafify (pullbackTensorComparison f G H) U _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ (TensorSheafification.toSheafify X.O.obj
        (Tensor.ringSheaf X.O).property
        ((f.pullbackModules.obj F).val ⊗
          (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H).val)).app U
      (((structureAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U a ⊗ₜ z))
    (comparison_val_app_unit_canonicalPairing f G H U b c)) ?_
  refine Eq.trans ?_ (pairingApp₃_prodMap_comp (invImageCanonicalPairing f F G) _ U a b c).symm
  refine Eq.trans ?_ (pairingApp_invChainPairing f (F ⊗ G) H _
    ((pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
      (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
        (f.pullbackModules.obj H)).hom) U _ c).symm
  refine Eq.trans ?_ (comp_val_app_apply
    (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H)
    (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
      (f.pullbackModules.obj H)).hom U _).symm
  refine Eq.trans ?_ (congrArg (fun z ↦ (α_ (f.pullbackModules.obj F)
        (f.pullbackModules.obj G) (f.pullbackModules.obj H)).hom.val.app U z)
    (whiskerRight_val_app_toSheafify (pullbackTensorComparison f F G) U _ _)).symm
  refine Eq.trans ?_ (congrArg (fun z ↦ (α_ (f.pullbackModules.obj F)
        (f.pullbackModules.obj G) (f.pullbackModules.obj H)).hom.val.app U
      ((TensorSheafification.toSheafify X.O.obj (Tensor.ringSheaf X.O).property
        (((f.pullbackModules.obj F) ⊗ (f.pullbackModules.obj G)).val ⊗
          (f.pullbackModules.obj H).val)).app U
        (z ⊗ₜ ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj H)).val.app U c)))
    (comparison_val_app_unit_canonicalPairing f F G U a b)).symm
  exact (associator_hom_val_app_tmul X.O.obj (Tensor.ringSheaf X.O).property
    (f.pullbackModules.obj F) (f.pullbackModules.obj G) (f.pullbackModules.obj H) U
    _ _ _).symm

open Stacks.SheafOfModules in
/-- **The residual identity of `associativity_of_residual`, discharged**: the two triple pairings
of `f⁻¹F`, `f⁻¹G` and `f⁻¹H` over `f⁻¹O_D` which the two sides of the associativity coherence
produce agree. Steps 1 to 3 of the three-variable chain eliminate both comparisons and the
pullback of the associator, leaving the identity `residual_pairing`. -/
theorem residual_associativity (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    assocTrilinearEquiv f F G H
        (f.pullbackModules.obj F ⊗
          (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
        (f.pullbackModules.map (α_ F G H).hom ≫ pullbackTensorComparison f F (G ⊗ H) ≫
          (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H)) =
      assocTrilinearEquiv f F G H
        (f.pullbackModules.obj F ⊗
          (f.pullbackModules.obj G ⊗ f.pullbackModules.obj H))
        (pullbackTensorComparison f (F ⊗ G) H ≫
          (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
            (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
              (f.pullbackModules.obj H)).hom) :=
  Subtype.ext
    ((assocTrilinearEquiv_pullbackMap_comparison_comp f F G H _
          (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H)).trans
      ((residual_pairing f F G H).trans
        (assocTrilinearEquiv_comparison_left_comp f F G H _
          ((pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
            (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
              (f.pullbackModules.obj H)).hom)).symm))

/-- **The associativity coherence of Tag 03EL**: the comparison
`Stacks.SheafOfModules.pullbackTensorIso` is compatible with the associator of the monoidal
structure of Tag 01CA. This is the field
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity`, character for
character, at **independent** coefficient universes — no unit comparison occurs in it, and so
nothing here identifies the two. -/
theorem associativity (F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map (α_ F G H).hom ≫ pullbackTensorComparison f F (G ⊗ H) ≫
        (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H) =
      pullbackTensorComparison f (F ⊗ G) H ≫
        (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
          (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
            (f.pullbackModules.obj H)).hom :=
  associativity_of_residual f F G H (residual_associativity f F G H)

end Coherence

end Stacks.SheafOfModules.RingedToposPullback

end
