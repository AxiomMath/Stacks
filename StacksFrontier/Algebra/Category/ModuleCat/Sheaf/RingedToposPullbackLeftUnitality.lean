module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorValue

/-!
# The left-unitality coherence of Tag 03EL

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The field
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.leftUnitality` asks that the
comparison `Stacks.SheafOfModules.pullbackTensorIso` of **Tag 03EL** be compatible with the left
unitor of the monoidal structure of Tag 01CA, the unit object being matched by
`Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison`:

`f^*(λ_F) = δ_{1, F} ≫ (ν ▷ f^*F) ≫ λ_{f^*F}`.

This file **proves that coherence**, at independent coefficient universes, by evaluating the
chain of six bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv` which *defines* the
comparison on a pure tensor of local sections. The evaluation is split in two: the first three
steps carry `f^*(λ_F)` to the pairing `(t, x) ↦ t • (1 ⊗ x)` over `f⁻¹O_D`, and the last three
carry `(ν ▷ f^*F) ≫ λ` to the pairing `(t, x) ↦ f♯(t) · (1 ⊗ x)`. The two agree because the unit
of Tag 03CZ is semilinear over `f♯`.

## Main results

* `leftUnitality`: **the coherence**, character for character the field
  `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.leftUnitality`, at the structure's
  own universes.
* `leftUnitality_of_residual`: the coherence from one identity of pairings over `f⁻¹O_D`;
  `residual_leftUnitality` is that identity. Both are at **independent** coefficient
  universes.
* `leftUnitality_of_pairing`: the coherence follows from the identity of pairings over `f⁻¹O_D`
  which step 3 of the chain produces. The three remaining steps are peeled off by the
  injectivity of the chain, which is what `Stacks.Sheaves.DerivedPullback`.`
  `pullbackTensorComparisonHom_comp` buys.
* `step1_leftUnitor`, `step2_leftUnitor`, `step3_leftUnitor`: **steps 1 to 3 of the chain,
  evaluated on `f^*(λ_F)`.** The answer is the scalar action of `f⁻¹O_D` on `f⁻¹F` followed by
  the unit of Tag 03CZ, informally `(t, x) ↦ t • (1 ⊗ x)`.
* `step123_pairingApp` and `step456_pairingApp`: the two pairings read on a pair of local
  sections. Both are `f♯(a) · (1 ⊗ b)`, which is what `residual_leftUnitality` says.
* `extendScalarsTensorIso_hom_val_app_unit_tmul`: **the value of step 6 of the chain on the
  sheafification unit of a local pure tensor**, `1 ⊗ (a ⊗ b) ↦ (1 ⊗ a) ⊗ (1 ⊗ b)`. This one is
  about base change of sheaves of modules along a morphism of presheaves of commutative rings
  and mentions no morphism of ringed topoi.

## Implementation notes

**The unit of Tag 03D3 cancels, and that is why no direct image on sections is needed.** Step 1
is the adjunction of Tag 03D7, which is the adjunction of Tag 03D3 composed with that of
Tag 03CZ, so its unit is the unit of Tag 03D3 followed by the direct image of the unit of
Tag 03CZ; and on underlying sheaves of sets the unit of Tag 03D3 *is* the unit of the adjunction
of the underlying topoi (`moduleSheafFunctor_map_invImageUnit`). Step 3 transposes back along
that same adjunction. The two therefore cancel by the triangle identity
(`invImage_pullbackUnit_comp_counit`), and the only trace the direct image leaves is the unit of
Tag 03CZ, which *does* have a formula on sections. This is what replaces the reading of a direct
image on sections, which for a `CategoryTheory.Sheaf.MorphismOfTopoi` does not exist — see
`Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv`, whose value formula stops at the
unit for exactly that reason.

**Ascriptions.** `leftUnitorHom` and `unitSMulHom` are `λ_F` and the scalar action with their
sources ascribed at the spellings the chain uses — the tensor bifunctor of Tag 0GMW for the
first, the underlying sheaf of the unit object for the second. Both are the identity on the
nose. Without them a goal containing those morphisms is not type-correct at `reducible`
transparency and `rw` reports a missing pattern rather than the cause; this is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal`. For the same reason
`reassoc₄` supplies its reassociation at objects which are all variables, and the peeling of the
chain in `leftUnitality_of_pairing` is a term rather than a sequence of rewrites.

**Universes: the whole file is at independent coefficient universes.** Every declaration,
`leftUnitality` included, is stated for `X : RingedTopos.{v, u, w}` and
`Y : RingedTopos.{v', u', w'}` with the two sites and the two coefficient universes
**independent**, exactly as for `PullbackCoherence` itself. Nothing here assumes `Small` or
`EssentiallySmall`, identifies the two site universes, or inserts a universe-lifting comparison.

The section formula `ν : f^*O_D ≅ O_C` —
`Stacks.Sheaves.RingedToposModules`.
`moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv` — rests on
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, and this needs no identification of the
coefficient universes: `pullbackModuleUnitIso` is `Iso.refl` between two objects that are
definitionally equal whatever the two coefficient universes are. It therefore has a section of
its own at independent coefficient universes, apart from the finite-free comparison beside it,
where identifying the two universes *is* forced, by the index type of
`Stacks.SheafOfModules.free`. So no universe restriction enters `Stacks.Sheaves.FinitePresentation`.
`pullbackModulesUnitIso`, the `ν` formula, or this file.

`leftUnitality_of_residual` is unchanged: it always accepted a residual proved at any universe
configuration, and is now handed one at the general configuration. `structureAdjunction` is
likewise unchanged, and is now literally `Stacks.Sheaves.RingedToposModules.fSharpAdjunction`
with its arguments written out — the two may be merged, which this change does not do.

**The seams, and why every step is a term.** The computation crosses three spellings of the
sheaf of rings `f⁻¹O_D` — `inverseImageRingSheaf`, `commRingSheaf` of
`inverseImageStructureCommRing`, and the module `moduleSheaf` of the inverse image of the unit
object, which is the sheaf of rings itself — and two spellings of `O_C`. They agree by `rfl` and
by proof irrelevance but not syntactically, so `rw` reports a missing pattern rather than the
cause: the first rewrite of `extendScalarsTensorIso_hom_val_app_unit_tmul` was written three
ways as a tactic before being supplied as a term. Every naturality square used below is
therefore stated in **applied** form — at one object and on one section — because no
composite-unfolding lemma fires on a composite read through `CategoryTheory.ConcreteCategory.hom`,
and every reassociation happens inside a `congrArg` whose function carries an explicit type
ascription.

## What this file does not contain

**`PullbackCoherence` itself.** Only its `leftUnitality` field is proved here;
`associativity` and `rightUnitality` are untouched, so the structure is not constructed and the
monoidal structure it buys is not available. The associativity field in particular still needs
the transport of *triple* pairings across `f⁻¹ ⊣ f_*`, which exists in no form.

**No monoidal instance.** Nothing here registers a `Monoidal` or `LaxMonoidal` instance.

**No identification of `Stacks.Sheaves.RingedToposModules.extendScalarsFSharpMonoidal`.** The
coherence proved here is, after the reduction, the oplax left unitality of extension of scalars
along `f♯`, and that functor already carries a `CategoryTheory.Functor.Monoidal` instance; but
no lemma identifies that instance's `δ` and `η` with
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` and with `ν`, so the instance cannot
be used to shorten anything below and nothing here supplies such a lemma.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
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

/-- The left unitor of the structure of Tag 01CA, with its source ascribed at the tensor
bifunctor of Tag 0GMW. The ascription is what makes a goal containing it type-correct at
`reducible` transparency, so that `rw` can work inside it; see the module documentation of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal`. -/
def leftUnitorHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (𝟙_ (_root_.SheafOfModules.{w'}
        (Tensor.ringSheaf Y.O)))).obj F ⟶ F :=
  (λ_ F).hom

/-- The adjunction of Tag 03CZ along the inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure
map. This is `Stacks.Sheaves.RingedToposModules.fSharpAdjunction` with its arguments written out.
It was introduced because that abbreviation, declared in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue`, sat under a variable
block identifying the two coefficient universes, which this file needs independent. That block no
longer identifies them, so the two abbreviations now say the same thing and may be merged. -/
abbrev structureAdjunction :=
  f.extendRestrictScalarsFSharpAdjunction

/-- The scalar action of the structure sheaf, with its source ascribed at the underlying sheaf
of sets of the unit object `𝟙_` of the structure of Tag 01CA rather than at the sheaf of rings.
The two agree by definition; the ascription is what keeps a goal containing this morphism
type-correct at `reducible` transparency, so that `rw` can work inside it. -/
def unitSMulHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ⨯
        Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F ⟶
      Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F :=
  Sheaf.moduleSMulHom (Tensor.ringSheaf Y.O) F

/-- reduction -/
theorem eq_comparison_comp {F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)}
    {N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
    (h : f.pullbackModules.obj (F ⊗ G) ⟶ N)
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj G ⟶ N)
    (hk : Stacks.SheafOfModules.pullbackTensorHomEquiv f F G N h = k) :
    h = pullbackTensorComparison f F G ≫ k :=
  ((Equiv.eq_symm_apply (Stacks.SheafOfModules.pullbackTensorHomEquiv f F G N)).2 hk).trans
    (Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp f F G k).symm


open Stacks.SheafOfModules in
/-- The chain, applied, as the six nested steps. -/
theorem chain_apply (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (h : f.pullbackModules.obj (F ⊗ G) ⟶ N) :
    pullbackTensorHomEquiv f F G N h =
      pullbackTensorStep6 f F G N (pullbackTensorStep5 f F G N (pullbackTensorStep4 f F G N
        (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
          (pullbackTensorStep1 f F G N h))))) :=
  rfl

open Stacks.SheafOfModules in
/-- Peeling the last three steps of the chain: the left-unitality coherence follows from the
single identity of pairings over `f⁻¹O_D` which step 3 of the chain of Tag 03EL produces. -/
theorem leftUnitality_of_pairing (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (hP : pullbackTensorStep3 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
          (f.pullbackModules.obj F)
          (pullbackTensorStep2 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
            (f.pullbackModules.obj F)
            (pullbackTensorStep1 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F) (f.pullbackModules.map (leftUnitorHom F)))) =
        (pullbackTensorStep4 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
            (f.pullbackModules.obj F)).symm
          ((pullbackTensorStep5 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep6 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                (f.pullbackModules.obj F)).symm
              (((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
                (λ_ (f.pullbackModules.obj F)).hom)))) :
    f.pullbackModules.map (λ_ F).hom =
      pullbackTensorComparison f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F ≫
        ((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
          (λ_ (f.pullbackModules.obj F)).hom :=
  eq_comparison_comp f _ _ ((chain_apply f _ F _ _).trans
    ((congrArg (pullbackTensorStep6 f _ F _)
      ((congrArg (pullbackTensorStep5 f _ F _)
        ((congrArg (pullbackTensorStep4 f _ F _) hP).trans
          (Equiv.apply_symm_apply _ _))).trans
        (Equiv.apply_symm_apply _ _))).trans (Equiv.apply_symm_apply _ _)))

open Stacks.SheafOfModules in
/-- Step 1 of the chain on the pullback of the left unitor: the adjunction of Tag 03D7 carries
`f^*(λ_F)` to `λ_F` followed by the unit. -/
theorem step1_leftUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    pullbackTensorStep1 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
        (f.pullbackModules.obj F) (f.pullbackModules.map (leftUnitorHom F)) =
      leftUnitorHom F ≫ (pullbackAdjPushforwardModules f).unit.app F :=
  ((pullbackAdjPushforwardModules f).homEquiv_unit _ _ _).trans
    ((pullbackAdjPushforwardModules f).unit.naturality (leftUnitorHom F)).symm

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
open Stacks.SheafOfModules in
/-- The value on local sections of the pairing produced by step 2 of the chain. -/
theorem pairingApp_step2 (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G ⟶
      (pushforwardModules f).obj N)
    (U : Y.Cᵒᵖ) (a : F.val.obj U) (b : G.val.obj U) :
    pairingApp (Tensor.ringSheaf Y.O) (pullbackTensorStep2 f F G N t).1 U a b =
      t.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Tensor.ringSheaf Y.O) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
          (a ⊗ₜ[(Y.O.obj ⋙ forget₂ CommRingCat.{w'} RingCat.{w'}).obj U] b)) :=
  pairingApp_bilinearEquivTensorSheafHom_symm (hA := (Tensor.ringSheaf Y.O).property) t U a b

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
open Stacks.SheafOfModules in
/-- The pairing of the left unitor followed by a morphism is the scalar action followed by it. -/
theorem step2_leftUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (m : F ⟶ (pushforwardModules f).obj N) :
    (pullbackTensorStep2 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F N
        (leftUnitorHom F ≫ m)).1 =
      unitSMulHom F ≫ (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map m :=
  pairing_ext (Tensor.ringSheaf Y.O) fun U r a ↦
    (pairingApp_step2 f _ F N (leftUnitorHom F ≫ m) U r a).trans
      ((congrArg (fun z ↦ m.val.app U z)
          (Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul Y.O.obj _ F U r a)).trans
        (sectionsFunctor_map_moduleSMulHom_comp
          ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map m) U r a).symm)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the scalar action is the scalar action of the inverse image, with the
product comparison cancelled against the preservation isomorphism. -/
theorem invImage_moduleSMulHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (PreservesLimitPair.iso f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)).inv ≫
        f.toToposHom.inverseImage.map (unitSMulHom F) =
      Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) :=
  (congrArg (fun z ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)).inv ≫ z)
      (Stacks.Sheaves.ToposPullback.moduleSMul_map_aux' X.J f.toToposHom.inverseImage
        (Tensor.ringSheaf Y.O) F)).trans
    (Iso.inv_hom_id_assoc _ _)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The unit of the adjunction of Tag 03D3 is, on underlying sheaves of sets, the unit of the
adjunction of the underlying topoi. -/
theorem moduleSheafFunctor_map_invImageUnit
    (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((inverseImageAdjDirectImageModules f.toToposHom (Tensor.ringSheaf Y.O)).unit.app F) =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F) :=
  (moduleSheafFunctor_map_toposModulesHomEquiv f.toToposHom (Tensor.ringSheaf Y.O)
      (𝟙 ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))).trans
    ((congrArg (f.toToposHom.adj.homEquiv _ _)
        ((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map_id _)).trans
      (f.toToposHom.adj.homEquiv_id _))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The unit of the adjunction of Tag 03D7, on underlying sheaves of sets: the unit of the
adjunction of topoi followed by the direct image of the underlying map of the unit of
Tag 03CZ. -/
theorem moduleSheafFunctor_map_pullbackUnit
    (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F) =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F) ≫
        f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) :=
  (congrArg (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        (Adjunction.comp_unit_app
          (inverseImageAdjDirectImageModules f.toToposHom (Tensor.ringSheaf Y.O))
          (structureAdjunction f) F)).trans
    (((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map_comp _ _).trans
      (congrArg₂ (fun p q ↦ p ≫ q) (moduleSheafFunctor_map_invImageUnit f F)
        (moduleSheafFunctor_map_directImageModules_map f.toToposHom (Tensor.ringSheaf Y.O) _)))

/-- Reassociation of a four-fold composite, stated with every object a variable so that `rw`
finds the pattern at objects whose spellings it cannot decide. -/
lemma reassoc₄ {E : Type*} [Category E] {A B D G H : E}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ G) (d : G ⟶ H) :
    a ≫ (b ≫ c) ≫ d = (a ≫ b) ≫ c ≫ d :=
  (congrArg (fun z ↦ a ≫ z) (Category.assoc b c d)).trans (Category.assoc a b (c ≫ d)).symm

/-- Cancelling a unit against a counit: the transpose of a transpose. -/
lemma adj_unit_counit_cancel {E : Type*} [Category E] {D : Type*} [Category D]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) {A : D} {B : E} (y : L.obj A ⟶ B) :
    L.map (adj.unit.app A ≫ R.map y) ≫ adj.counit.app B = y :=
  (congrArg (fun z ↦ L.map z ≫ adj.counit.app B) (adj.homEquiv_unit A B y).symm).trans
    ((adj.homEquiv_counit A B (adj.homEquiv A B y)).symm.trans
      ((adj.homEquiv A B).symm_apply_apply y))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The inverse image of the unit of Tag 03D7, followed by the counit of the adjunction of
topoi, is the unit of Tag 03CZ**, on underlying sheaves of sets. This is the triangle identity:
the topos half of the composite unit is the unit of the adjunction of topoi, and step 3 of the
chain transposes back along that same adjunction. -/
theorem invImage_pullbackUnit_comp_counit
    (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F)) ≫
        f.toToposHom.adj.counit.app
          (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
              (f.pullbackModules.obj F))) =
      (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
        ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) :=
  (congrArg (fun z ↦ f.toToposHom.inverseImage.map z ≫
        f.toToposHom.adj.counit.app
          (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
              (f.pullbackModules.obj F))))
      (moduleSheafFunctor_map_pullbackUnit f F)).trans
    (adj_unit_counit_cancel f.toToposHom.adj _)

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on the pullback of the left unitor.** The pairing
over `f⁻¹O_D` they produce is the scalar action of `f⁻¹O_D` on `f⁻¹F` followed by the unit of
Tag 03CZ: informally `(t, x) ↦ t • (1 ⊗ x)`.

The unit of Tag 03D3 is carried to the unit of the adjunction of the underlying topoi, and step 3
transposes back along that same adjunction, so the two cancel against each other by the triangle
identity; nothing about a direct image on sections is needed. -/
theorem step3_leftUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (pullbackTensorStep3 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
          (f.pullbackModules.obj F)
          (pullbackTensorStep2 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
            (f.pullbackModules.obj F)
            (pullbackTensorStep1 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F) (f.pullbackModules.map (leftUnitorHom F))))).1 =
      Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) := by
  refine Eq.trans (congrArg (fun z ↦ (pullbackTensorStep3 f
      (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F (f.pullbackModules.obj F)
      (pullbackTensorStep2 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
        (f.pullbackModules.obj F) z)).1) (step1_leftUnitor f F)) ?_
  refine Eq.trans (inverseImageBilinearEquiv_symm_apply_coe_eq_comp_counit f.toToposHom
    (Tensor.ringSheaf Y.O) (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)).inv ≫
      f.toToposHom.inverseImage.map m ≫ f.toToposHom.adj.counit.app _)
    (step2_leftUnitor f F (f.pullbackModules.obj F)
      ((pullbackAdjPushforwardModules f).unit.app F))) ?_
  refine Eq.trans (congrArg (fun z ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)).inv ≫ z ≫
      f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            (f.pullbackModules.obj F))))
    (f.toToposHom.inverseImage.map_comp (unitSMulHom F)
      ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F)))) ?_
  exact (reassoc₄ _ _ _ _).trans
    (congrArg₂ (fun p q ↦ p ≫ q) (invImage_moduleSMulHom f F)
      (invImage_pullbackUnit_comp_counit f F))

open Stacks.SheafOfModules in
/-- **The left-unitality coherence of Tag 03EL, from one explicit identity.** Everything the
chain of Tag 03EL contributes is discharged here: what is left is the single identity `h`,
between two morphisms of sheaves of sets over `f⁻¹O_D`, in which the comparison of Tag 03EL no
longer occurs and no transpose of it is taken. Informally `h` says that `t • (1 ⊗ x)` and
`f♯(t) · (1 ⊗ x)` agree, the left-hand side being the pairing `steps 1–3` produce and the
right-hand side the one `(ν ▷ -) ≫ λ` produces through `steps 4–6`. -/
theorem leftUnitality_of_residual (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (h : Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) =
        ((pullbackTensorStep4 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep5 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                (f.pullbackModules.obj F)).symm
              ((pullbackTensorStep6 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                  (f.pullbackModules.obj F)).symm
                (((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
                  (λ_ (f.pullbackModules.obj F)).hom)))).1) :
    f.pullbackModules.map (λ_ F).hom =
      pullbackTensorComparison f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F ≫
        ((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
          (λ_ (f.pullbackModules.obj F)).hom :=
  leftUnitality_of_pairing f F (Subtype.ext ((step3_leftUnitor f F).trans h))

/-! ## Step 6 of the chain on a local pure tensor

The statements of this section are about base change of sheaves of modules along a morphism
`θ : A₁ ⟶ A₂` of presheaves of commutative rings, and mention no morphism of ringed topoi: they
are the value of step 6 of the chain of Tag 03EL, read on a local pure tensor. Each naturality
square is stated in **applied** form, at one object and on one section, because no
composite-unfolding lemma fires on a composite read through `ConcreteCategory.hom`. -/

section BaseChange

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The unit of the adjunction of Tag 03CZ on a local section**, through the presheaf-level
change-of-rings unit: it is the sheafification unit of `1 ⊗ x`, with the `1 ⊗ (-)` left as the
unit of the adjunction of Tag 03CU so that no algebra instance has to be named. This is
`Stacks.Sheaves.RingedToposModules.forget_map_extendRestrictScalarsAdjunction_unit_app`, read at
one object. -/
theorem extendRestrictScalarsAdjunction_unit_val_app
    (L : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : Cᵒᵖ) (x : L.val.obj U) :
    ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val.app U x =
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj L.val)).app U
        (((changeOfRingsAdjunction θ).unit.app L.val).app U x) :=
  congrArg (fun m ↦ m.app U x)
    (forget_map_extendRestrictScalarsAdjunction_unit_app J θ h₁ h₂ L)

/-- Naturality of the unit of the adjunction of Tag 03CU, on a local section. -/
theorem changeOfRingsAdjunction_unit_naturality_app
    {P Q : PresheafOfModules.{w} (ringPresheaf A₁)} (φ : P ⟶ Q) (U : Cᵒᵖ) (y : P.obj U) :
    ((changeOfRingsAdjunction θ).unit.app Q).app U (φ.app U y) =
      ((changeOfRings θ).map φ).app U
        (((changeOfRingsAdjunction θ).unit.app P).app U y) :=
  congrArg (fun m ↦ m.app U y) ((changeOfRingsAdjunction θ).unit.naturality φ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Naturality of the sheafification unit of presheaves of `A₂`-modules, on a local section:
sheafifying a morphism acts on the image of a section by acting on the section. -/
theorem sheafificationUnit_naturality_app
    {P Q : PresheafOfModules.{w} (ringPresheaf A₂)} (φ : P ⟶ Q) (U : Cᵒᵖ) (y : P.obj U) :
    ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map φ).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app P).app U y) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app Q).app U (φ.app U y) :=
  congrArg (fun m ↦ m.app U y)
    ((PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.naturality φ).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Step 6 of the chain of Tag 03EL on a sheafification-unit section**, the inverse of its
first factor eliminated. This is
`Stacks.Sheaves.RingedToposModules.changeOfRingsUnit_comp_extendScalarsTensorIso_hom`, read at
one object and with `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnit` written out as
the change-of-rings image of a sheafification unit. -/
theorem extendScalarsTensorIso_hom_val_app_sheafifyUnit
    (L₁ L₂ : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : Cᵒᵖ)
    (y : ((changeOfRings θ).obj (L₁.val ⊗ L₂.val)).obj U) :
    (extendScalarsTensorIso θ h₁ h₂ L₁ L₂).hom.val.app U
        (((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
              ((changeOfRings θ).map
                ((PresheafOfModules.sheafificationAdjunction
                  (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app
                    (L₁.val ⊗ L₂.val)))).val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((changeOfRings θ).obj (L₁.val ⊗ L₂.val))).app U y)) =
      ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          (((extendScalars J θ h₁ h₂).obj L₁).val ⊗
            ((extendScalars J θ h₁ h₂).obj L₂).val)).app U
        (((changeOfRingsTensorObjIso θ L₁.val L₂.val).hom ≫
            ((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj L₁.val) ⊗ₘ
              (PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
                  ((changeOfRings θ).obj L₂.val))).app U y) :=
  (congrArg (fun m ↦ m.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj (L₁.val ⊗ L₂.val))).app U y))
      (changeOfRingsUnit_comp_extendScalarsTensorIso_hom θ h₁ h₂ L₁ L₂)).trans
    (sheafificationUnit_naturality_app h₂ _ U y)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The presheaf-level comparison of Tag 03CU on `1 ⊗ (a ⊗ b)`**, followed by the tensor of
two sheafification units: it is the pure tensor of `1 ⊗ a` and `1 ⊗ b`. The comparison is
`TensorProduct.AlgebraTensorModule.distribBaseChange` in each component. -/
theorem changeOfRingsTensorObjIso_hom_app_unit_tmul
    (L₁ L₂ : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : Cᵒᵖ)
    (a : L₁.val.obj U) (b : L₂.val.obj U) :
    ((changeOfRingsTensorObjIso θ L₁.val L₂.val).hom ≫
          ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj L₁.val) ⊗ₘ
            (PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
                ((changeOfRings θ).obj L₂.val))).app U
        (((changeOfRingsAdjunction θ).unit.app (L₁.val ⊗ L₂.val)).app U
          (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj L₁.val)).app U
          (((changeOfRingsAdjunction θ).unit.app L₁.val).app U a) ⊗ₜ
        ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj L₂.val)).app U
          (((changeOfRingsAdjunction θ).unit.app L₂.val).app U b) := by
  let := (θ.app U).hom.toAlgebra
  rw (transparency := .default) [changeOfRingsAdjunction_unit_app_apply,
    changeOfRingsAdjunction_unit_app_apply, changeOfRingsAdjunction_unit_app_apply]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The sheafification unit of a local pure tensor, carried through the unit of Tag 03CZ and
step 6 of the chain of Tag 03EL.** The answer is the local pure tensor of the two units of
Tag 03CZ: informally `1 ⊗ (a ⊗ b) ↦ (1 ⊗ a) ⊗ (1 ⊗ b)`. -/
theorem extendScalarsTensorIso_hom_val_app_unit_tmul
    (L₁ L₂ : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : Cᵒᵖ)
    (a : L₁.val.obj U) (b : L₂.val.obj U) :
    (extendScalarsTensorIso θ h₁ h₂ L₁ L₂).hom.val.app U
        (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj L₁).obj L₂))).val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (L₁.val ⊗ L₂.val)).app U
            (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))) =
      ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          (((extendScalars J θ h₁ h₂).obj L₁).val ⊗
            ((extendScalars J θ h₁ h₂).obj L₂).val)).app U
        (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L₁).val.app U a ⊗ₜ
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L₂).val.app U b) :=
  (congrArg (fun z ↦ (extendScalarsTensorIso θ h₁ h₂ L₁ L₂).hom.val.app U z)
      (extendRestrictScalarsAdjunction_unit_val_app θ h₁ h₂
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj L₁).obj L₂)) U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (L₁.val ⊗ L₂.val)).app U
          (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)))).trans
    ((congrArg (fun z ↦ (extendScalarsTensorIso θ h₁ h₂ L₁ L₂).hom.val.app U
            (((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
              ((changeOfRings θ).obj
                ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _
                    A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj L₁).obj L₂)).val)).app U z))
        (changeOfRingsAdjunction_unit_naturality_app θ
          ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (L₁.val ⊗ L₂.val)) U
          (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))).trans
      ((congrArg (fun z ↦ (extendScalarsTensorIso θ h₁ h₂ L₁ L₂).hom.val.app U z)
            (sheafificationUnit_naturality_app h₂
              ((changeOfRings θ).map
                ((PresheafOfModules.sheafificationAdjunction
                  (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (L₁.val ⊗ L₂.val))) U
              (((changeOfRingsAdjunction θ).unit.app (L₁.val ⊗ L₂.val)).app U
                (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))).symm).trans
        ((extendScalarsTensorIso_hom_val_app_sheafifyUnit θ h₁ h₂ L₁ L₂ U
              (((changeOfRingsAdjunction θ).unit.app (L₁.val ⊗ L₂.val)).app U
                (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))).trans
          ((congrArg (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
                  (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
                (((extendScalars J θ h₁ h₂).obj L₁).val ⊗
                  ((extendScalars J θ h₁ h₂).obj L₂).val)).app U z)
              (changeOfRingsTensorObjIso_hom_app_unit_tmul θ h₁ h₂ L₁ L₂ U a b)).trans
            (congrArg₂ (fun p q ↦ ((PresheafOfModules.sheafificationAdjunction
                    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
                  (((extendScalars J θ h₁ h₂).obj L₁).val ⊗
                    ((extendScalars J θ h₁ h₂).obj L₂).val)).app U (p ⊗ₜ q))
              (extendRestrictScalarsAdjunction_unit_val_app θ h₁ h₂ L₁ U a).symm
              (extendRestrictScalarsAdjunction_unit_val_app θ h₁ h₂ L₂ U b).symm)))))

end BaseChange

/-! ## The residual -/

section Residual

open Stacks.PresheafOfModules.ChangeOfRings

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Right whiskering of the monoidal structure of Tag 01CA on a local pure tensor: it acts in
the first factor. -/
theorem whiskerRight_val_app_toSheafify
    {A A' B : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (a : A ⟶ A') (U : X.Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (a ▷ B).val.app U
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
          (Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
        (Tensor.ringSheaf X.O).property (A'.val ⊗ B.val)).app U (a.val.app U x ⊗ₜ y) :=
  (congrArg (fun m : A ⊗ B ⟶ A' ⊗ B ↦ m.val.app U
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
          (Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)))
      (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map X.O.obj
        (Tensor.ringSheaf X.O).property a B)).trans
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app X.O.obj
      (Tensor.ringSheaf X.O).property (a.val ▷ B.val) U (x ⊗ₜ y))


/-- **The value of `ν : f^*O_D ≅ O_C` on the unit of Tag 03CZ**: it is the inverse-image form
`f♯ : f⁻¹O_D ⟶ O_C` of the structure map, on local sections. This is
`Stacks.Sheaves.RingedToposModules`.
`moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`, with the
transpose written out as the unit followed by `ν` and both sides read at one object. -/
theorem pullbackUnitComparison_val_app_unit (U : X.Cᵒᵖ)
    (a : ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
      (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))).val.obj U) :
    (pullbackUnitComparison f).hom.val.app U
        (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).val.app U a) =
      (Sheaf.sectionsFunctor X.J U).map
        ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) a :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor X.J U).map m a)
    ((congrArg (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
        ((structureAdjunction f).homEquiv_unit _ _ (pullbackUnitComparison f).hom).symm).trans
      (moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv f))

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit of Tag 03CZ is semilinear over `f♯`**: a scalar of `f⁻¹O_D` comes out of it as
its image under `f♯ : f⁻¹O_D ⟶ O_C`. The first step is the linearity of the unit over
`f⁻¹O_D`, the second the identification of the `f⁻¹O_D`-action on a restriction of scalars. -/
theorem structureAdjunction_unit_sections_smul
    (L : _root_.SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.ringSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)) L)) :
    (Sheaf.sectionsFunctor X.J U).map
        ((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app L)) (r • b) =
      Sheaf.moduleSMulObj (Tensor.ringSheaf X.O) ((extendScalarsFSharp f).obj L)
        (Sheaf.sectionsFunctor X.J U)
        ((Sheaf.sectionsFunctor X.J U).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) r)
        ((Sheaf.sectionsFunctor X.J U).map
          ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app L)) b) :=
  ((moduleSMulHom_comp_iff _).mp
        (moduleSMulHom_comp_moduleSheafFunctor_map ((structureAdjunction f).unit.app L))
        U r b).trans
    ((Sheaf.sectionsFunctor_map_moduleSMulHom _ _ U r _).symm.trans
      (moduleSMulObj_restrictScalars
        (commRingSheafMap X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)).property
          (Tensor.ringSheaf X.O).property)
        ((extendScalarsFSharp f).obj L) (Sheaf.sectionsFunctor X.J U) r _))

/-- **Steps 4 to 6 of the chain of Tag 03EL, inverted, on `(ν ▷ f^*F) ≫ λ`**, read on a pair of
local sections: the pairing they produce carries `(a, b)` to `f♯(a) · (1 ⊗ b)`. -/
theorem step456_pairingApp (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
        (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((pullbackTensorStep4 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep5 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                (f.pullbackModules.obj F)).symm
              ((pullbackTensorStep6 f
                  (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                  (f.pullbackModules.obj F)).symm
                (((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
                  (λ_ (f.pullbackModules.obj F)).hom)))).1 U a b =
      Sheaf.moduleSMulObj (Tensor.ringSheaf X.O) (f.pullbackModules.obj F)
        (Sheaf.sectionsFunctor X.J U)
        ((Sheaf.sectionsFunctor X.J U).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) a)
        (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U b) :=
  (pairingApp_bilinearEquivTensorSheafHom_symm
        (hA := isSheaf_inverseImageStructureCommRing f) _ U a b).trans
    ((congrArg (fun m : inverseImageTensorSheaf f
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
              (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ⟶
          (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            (f.pullbackModules.obj F) ↦ m.val.app U _)
          ((structureAdjunction f).homEquiv_unit _ _ _)).trans
      ((congrArg (fun z ↦ (((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
              (λ_ (f.pullbackModules.obj F)).hom).val.app U z)
          (extendScalarsTensorIso_hom_val_app_unit_tmul (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)).property
            (Tensor.ringSheaf X.O).property
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
              (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) U a b)).trans
        ((congrArg (fun z ↦ (λ_ (f.pullbackModules.obj F)).hom.val.app U z)
              (whiskerRight_val_app_toSheafify (pullbackUnitComparison f).hom U _ _)).trans
          ((Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul X.O.obj _
                (f.pullbackModules.obj F) U _ _).trans
            ((Sheaf.sectionsFunctor_map_moduleSMulHom (Tensor.ringSheaf X.O)
                  (f.pullbackModules.obj F) U _ _).symm.trans
              (congrArg (fun ρ ↦ Sheaf.moduleSMulObj (Tensor.ringSheaf X.O)
                  (f.pullbackModules.obj F) (Sheaf.sectionsFunctor X.J U) ρ _)
                (pullbackUnitComparison_val_app_unit f U a)))))))

/-- **Steps 1 to 3 of the chain of Tag 03EL on `f^*(λ_F)`**, read on a pair of local sections:
the pairing `step3_leftUnitor` produces carries `(a, b)` to `1 ⊗ (a · b)`, which is
`f♯(a) · (1 ⊗ b)` by semilinearity of the unit of Tag 03CZ. -/
theorem step123_pairingApp (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
        (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        (Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) U a b =
      Sheaf.moduleSMulObj (Tensor.ringSheaf X.O) (f.pullbackModules.obj F)
        (Sheaf.sectionsFunctor X.J U)
        ((Sheaf.sectionsFunctor X.J U).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) a)
        (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U b) :=
  ((Sheaf.sectionsFunctor X.J U).map_comp_apply
        (Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))
        ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) _).trans
    ((congrArg (fun z ↦ (Sheaf.sectionsFunctor X.J U).map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) z)
        (Sheaf.sectionsFunctor_map_moduleSMulHom
          (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) U a b)).trans
      (structureAdjunction_unit_sections_smul f
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) U a b))

/-- **The residual identity, discharged**: the two pairings over `f⁻¹O_D` agree, because on a
pair of local sections both are `f♯(a) · (1 ⊗ b)`. This is the hypothesis of
`leftUnitality_of_residual`. -/
theorem residual_leftUnitality (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Sheaf.moduleSMulHom (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) =
      ((pullbackTensorStep4 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
            (f.pullbackModules.obj F)).symm
          ((pullbackTensorStep5 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep6 f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F
                (f.pullbackModules.obj F)).symm
              (((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
                (λ_ (f.pullbackModules.obj F)).hom)))).1 :=
  pairing_ext (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
    fun U a b ↦ (step123_pairingApp f F U a b).trans (step456_pairingApp f F U a b).symm

/-- **The left-unitality coherence of Tag 03EL**: the comparison of Tag 03EL is compatible with
the left unitor of the structure of Tag 01CA, the unit object being matched by
`ν : f^*O_D ≅ O_C`. This is the field
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.leftUnitality`,
character for character. -/
theorem leftUnitality (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map (λ_ F).hom =
      pullbackTensorComparison f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F ≫
        ((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
          (λ_ (f.pullbackModules.obj F)).hom :=
  leftUnitality_of_residual f F (residual_leftUnitality f F)

end Residual

end Stacks.SheafOfModules.RingedToposPullback

end
