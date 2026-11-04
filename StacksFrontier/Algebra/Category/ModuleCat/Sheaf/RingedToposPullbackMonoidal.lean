module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback along a morphism of ringed topoi as a monoidal functor

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. Both categories of
sheaves of modules carry the monoidal structure of Tag 01CA, whose tensor product is the tensor
product sheaf on the nose; `Stacks.SheafOfModules.pullbackTensorIso` is the comparison

`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G`

of **Tag 03EL**, and `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` is the
comparison `f^*O_D ≅ O_C` of the units. This file assembles the two into a monoidal structure on
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, and from it the lax monoidal
structure on `Stacks.Sheaves.RingedToposModules.pushforwardModules`.

**An isomorphism of bifunctors is not a monoidal structure**, and what is needed besides is
exactly the three coherences: the comparison has to be compatible with the associator and with
the two unitors. Those three are collected into the single named proposition
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`, which this file states and does
not discharge; it is discharged, unconditionally, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence`. Everything else here
is unconditional, and every statement which needs the coherence takes it as an explicit
argument — no monoidal hypothesis is left implicit, and no second monoidal instance is registered
on anything.

## Main definitions

* `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison` and
  `pullbackTensorComparisonIso`: the comparison of Tag 03EL, with its source and target ascribed
  at the monoidal product `⊗` of the structure of Tag 01CA.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison`: the comparison
  `ν : f^*O_D ≅ O_C`, with its source and target ascribed at the unit object `𝟙_`.
* `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`: the three coherences of the two
  comparisons, as one proposition. Proved in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence`.
* `Stacks.SheafOfModules.RingedToposPullback.coreMonoidal` and `monoidal`: the pullback as a
  monoidal functor, **given** a `PullbackCoherence`.
* `Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal`: the pushforward as a lax
  monoidal functor, **given** a `PullbackCoherence`; this is
  `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` at the adjunction of Tag 03D7, so its
  tensorator is the mate of the oplax tensorator of the pullback.

## Main results

* `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_naturality_left` and
  `..._naturality_right`: naturality of the comparison of Tag 03EL in each variable, in the
  whiskered form a monoidal coherence is phrased in. Unconditional.
* `Stacks.SheafOfModules.RingedToposPullback.moduleSheafPushforwardIso`: **the underlying sheaf
  of sets of a pushforward is the direct image of the underlying sheaf of sets**, as a natural
  isomorphism of functors. Unconditional, and the identity in each component.

## Implementation notes

**The ascription is what makes the coherences statable.** The source of the comparison of
Tag 03EL is spelled `f^*((Stacks.SheafOfModules.Tensor.sheafTensor Y.J).obj (F, G))`, and `F ⊗ G`
for the structure of Tag 01CA is a different term equal to it by `rfl`. A composite mixing the
two is not type-correct at `implicit` transparency, so `rw` refuses a goal containing it and
reports a missing pattern rather than the cause. `pullbackTensorComparison` is the comparison with
its type ascribed at the `⊗` spelling, every statement below uses it, and the crossing happens
once per declaration inside a defeq-tolerant `:=`. This is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal`, which does the same
assembly for a morphism of ringed *spaces*, and the structure of this file mirrors it.

**Universes.** `X : AlgebraicGeometry.RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}`:
the two sites and the two coefficient universes are **independent**, exactly as for
`Stacks.SheafOfModules.pullbackTensorIso`, and the coefficient universes are tied to the
respective ring universes only because Mathlib's monoidal structure on presheaves of modules is.
Nothing here assumes `Small` or `EssentiallySmall`, identifies the two site universes, or
restricts to a common coefficient universe. A consumer typed at a single `w` is the special case
`w = w'`; no universe-lifting comparison is needed to reach it, and none is used.

**Neither monoidal structure is left to instance synthesis.** Sheaves of modules carry the
localized structure of `Stacks.SheafOfModules.monoidalCategory` as well as the strict one of
Tag 01CA, so the strict one is named by the `@[instance_reducible] def` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor` and switched on with
`attribute [local instance]`. It is not exported as an instance here, which is also what keeps
this file from registering a second, competing monoidal pairing on a category that already has
one.

## What this file does not contain

**The three coherences themselves.** `PullbackCoherence` is not proved here. It is proved, all
three fields and unconditionally, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence`, as
`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`; the three fields come from the
three files named below. So `monoidal` and `pushforwardLaxMonoidal` are available without
hypotheses, through that assembly.

The comparison of Tag 03EL is defined by the chain of six bijections
`Stacks.SheafOfModules.pullbackTensorHomEquiv`, as the preimage of the identity; the only handle
on it is `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp`, which says that a
composite beginning with the comparison is the preimage under that chain of its second factor.
Each coherence is therefore equivalent to one identity *of morphisms out of a tensor product*
with the comparison eliminated — for the right unitor,
`pullbackTensorHomEquiv f A O_D (f^*A) (f^*(ρ_A)) = (𝟙 ⊗ ν) ≫ ρ_{f^*A}` — and what is owed is the
evaluation of the chain on a pure tensor of local sections, i.e. the ringed-topoi analogue of
`Stacks.PullbackAlgebra.comparison_pullbackUnit_unit_tmul` and of
`PresheafOfModules.delta_pullbackAdjUnit_tmul`. Neither of those transports: both are built from a
presheaf-level colimit model of the pullback, and for a `CategoryTheory.Sheaf.MorphismOfTopoi`
there is no such model.

The inventory in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence`
recorded three missing inputs, and that note is now out of date in all three:

* **the extensionality of bilinear pairings exists**, as `Stacks.SheafOfModules.pairing_ext`, and
  `PresheafOfModules.tensorSheaf_hom_ext₂` is the iterated pure-tensor extensionality the
  associativity coherence needs;
* **the value formula for step 6 of the chain exists**, as
  `Stacks.Sheaves.RingedToposModules.changeOfRingsUnit_comp_extendScalarsTensorIso_hom` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorValue`. Step 6 is
  `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, a three-fold composite whose first
  factor is used *inverted*; composing with that factor rather than inverting it leaves the whole
  comparison as a single `sheafification.map` of an explicit morphism of presheaves of modules,
  whose components are `TensorProduct.AlgebraTensorModule.distribBaseChange` followed by a tensor
  of two sheafification units. That is the one input shared by all three coherences.
* **the section formula for the unit comparison `ν : f^*O_D ≅ O_C` exists**, as
  `Stacks.Sheaves.RingedToposModules.fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv` and
  its underlying-sheaf form, in the same namespace,
  `moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue`. The comparison
  produced by `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` is identified there with
  the explicit `Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`, whose transpose along
  Stacks 03CZ is `f♯ : f⁻¹O_D ⟶ O_C` itself; informally `ν(c ⊗ t) = c · f♯(t)`. This holds at the
  independent coefficient universes this file is stated for.
  `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, which the explicit comparison rests on,
  was once stated at a single coefficient universe; that was incidental to it and has been
  lifted.

**All three fields are proved**, at this file's own universes, by
`Stacks.SheafOfModules.RingedToposPullback.associativity` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackAssociativity`,
`leftUnitality` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality` and
`rightUnitality` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackRightUnitality`, and assembled
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence` at
`X : RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}` with all four universes
independent — no field restricts them.

The associativity field uses the transport of *triple* pairings across
the adjunction `f⁻¹ ⊣ f_*`, the three-variable mirror of
`Stacks.SheafOfModules.inverseImageBilinearEquiv`; it is available as
`Stacks.SheafOfModules.inverseImageTrilinearEquiv` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTrilinear`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace Stacks.SheafOfModules.RingedToposPullback

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-! ### The underlying sheaf of sets of a pushforward -/

section Unconditional

variable (f : RingedToposHom X Y)

/-- **The underlying sheaf of sets of the pushforward of a sheaf of modules is the direct image
of its underlying sheaf of sets**, as an isomorphism of functors `Mod(O_C) ⥤ Sh(D)`:

`ν : (- ↦ underlying sheaf) ⋙ f_* ≅ f_*^{Mod} ⋙ (- ↦ underlying sheaf)`.

Both the objects and the morphisms agree definitionally
(`Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules` and
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_directImageModules_map`), so this is the
identity in each component; it is provided in isomorphism form for consumers whose hypotheses are
isomorphism-shaped. The forgetful functor to sheaves of sets is
`CategoryTheory.Sheaf.moduleSheafFunctor`; this library has no declaration named `toSetSheaf`. -/
@[sga "4 IV 13.2.3" "partial"]
def moduleSheafPushforwardIso :
    Sheaf.moduleSheafFunctor (Tensor.ringSheaf X.O) ⋙ f.toToposHom.pushforward ≅
      pushforwardModules f ⋙ Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
    (Category.id_comp _).symm)

/-- Each component of `moduleSheafPushforwardIso` is the identity. -/
@[simp]
lemma moduleSheafPushforwardIso_hom_app (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafPushforwardIso f).hom.app F = 𝟙 _ :=
  rfl

end Unconditional

/-! ### The two comparisons at the monoidal spelling -/

section Comparisons

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- **The comparison of Tag 03EL**, `f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G`, with source and target spelled
through the monoidal product of the structure of Tag 01CA. -/
def pullbackTensorComparison (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.obj (F ⊗ G) ⟶
      f.pullbackModules.obj F ⊗ f.pullbackModules.obj G :=
  (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (F, G)

/-- **The comparison of Tag 03EL as an isomorphism** at the monoidal spelling. -/
def pullbackTensorComparisonIso (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.obj (F ⊗ G) ≅
      f.pullbackModules.obj F ⊗ f.pullbackModules.obj G :=
  (Stacks.SheafOfModules.pullbackTensorIso f).app (F, G)

/-- The forward morphism of `pullbackTensorComparisonIso` is `pullbackTensorComparison`. -/
theorem pullbackTensorComparisonIso_hom
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (pullbackTensorComparisonIso f F G).hom = pullbackTensorComparison f F G :=
  rfl

/-- **The comparison `ν : f^*O_D ≅ O_C` of the structure sheaves**, with its source and target
ascribed at the unit object `𝟙_` of the structure of Tag 01CA. The ascription is needed for the
same reason as for `pullbackTensorComparison`. -/
def pullbackUnitComparison :
    f.pullbackModules.obj (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ≅
      𝟙_ (_root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :=
  (pullbackModulesObjUnitIso f).symm

/-! ### Naturality of the comparison in each variable -/

/-- Naturality of the comparison of Tag 03EL at a pair of morphisms. -/
private theorem pullbackTensorComparison_naturality
    {F F' G G' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (v : F ⟶ F') (u : G ⟶ G') :
    pullbackTensorComparison f F G ≫ (f.pullbackModules.map v ⊗ₘ f.pullbackModules.map u) =
      f.pullbackModules.map (v ⊗ₘ u) ≫ pullbackTensorComparison f F' G' := by
  rw [Strict.tensorHom_eq_tensorSheafBifunctor_map Y.O v u,
    Strict.tensorHom_eq_tensorSheafBifunctor_map X.O (f.pullbackModules.map v)
      (f.pullbackModules.map u)]
  exact ((Stacks.SheafOfModules.pullbackTensorIso f).hom.naturality
    ((v, u) : ((F, G) : _ × _) ⟶ (F', G'))).symm

/-- **Naturality of the comparison of Tag 03EL in the first variable**, in whiskered form: right
whiskering is the action of the tensor bifunctor on `(v, 𝟙)`, so this is the naturality square of
`Stacks.SheafOfModules.pullbackTensorIso` at `(v, 𝟙)`. -/
theorem pullbackTensorComparison_naturality_left
    {F F' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (v : F ⟶ F')
    (G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    pullbackTensorComparison f F G ≫
        (f.pullbackModules.map v ▷ f.pullbackModules.obj G) =
      f.pullbackModules.map (v ▷ G) ≫ pullbackTensorComparison f F' G := by
  simpa using pullbackTensorComparison_naturality f v (𝟙 G)

/-- **Naturality of the comparison of Tag 03EL in the second variable**, in whiskered form. -/
theorem pullbackTensorComparison_naturality_right
    (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    {G G' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (u : G ⟶ G') :
    pullbackTensorComparison f F G ≫
        (f.pullbackModules.obj F ◁ f.pullbackModules.map u) =
      f.pullbackModules.map (F ◁ u) ≫ pullbackTensorComparison f F G' := by
  simpa using pullbackTensorComparison_naturality f (𝟙 F) u

/-! ### The three coherences, as one proposition -/

/-- **The three coherences the comparisons of Tag 03EL and of `f^*O_D ≅ O_C` are owed before they
are a monoidal structure**: compatibility of `Stacks.SheafOfModules.pullbackTensorIso` with the
associator, and with each of the two unitors, the unit object being matched by
`pullbackUnitComparison`.

It is stated as one proposition so that the construction which consumes it —
`Stacks.SheafOfModules.RingedToposPullback.coreMonoidal` and everything downstream of it — takes
it as an explicit argument rather than postulating a monoidal structure. It is proved,
unconditionally, by `Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence`. -/
structure PullbackCoherence : Prop where
  /-- The comparison of Tag 03EL is compatible with the associator. -/
  associativity : ∀ F G H : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O),
    f.pullbackModules.map (α_ F G H).hom ≫ pullbackTensorComparison f F (G ⊗ H) ≫
        (f.pullbackModules.obj F ◁ pullbackTensorComparison f G H) =
      pullbackTensorComparison f (F ⊗ G) H ≫
        (pullbackTensorComparison f F G ▷ f.pullbackModules.obj H) ≫
          (α_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)
            (f.pullbackModules.obj H)).hom
  /-- The comparison of Tag 03EL is compatible with the left unitor, the unit object being
  matched by `ν : f^*O_D ≅ O_C`. -/
  leftUnitality : ∀ F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O),
    f.pullbackModules.map (λ_ F).hom =
      pullbackTensorComparison f (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) F ≫
        ((pullbackUnitComparison f).hom ▷ f.pullbackModules.obj F) ≫
          (λ_ (f.pullbackModules.obj F)).hom
  /-- The comparison of Tag 03EL is compatible with the right unitor, the unit object being
  matched by `ν : f^*O_D ≅ O_C`. -/
  rightUnitality : ∀ F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O),
    f.pullbackModules.map (ρ_ F).hom =
      pullbackTensorComparison f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ≫
        (f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
          (ρ_ (f.pullbackModules.obj F)).hom

/-! ### The monoidal structures the coherence buys -/

/-- **The pullback of sheaves of modules along a morphism of ringed topoi is a monoidal functor,
given the coherence**: this is `CategoryTheory.Functor.CoreMonoidal.mk'` applied to the two
naturality statements above and to the three coherences of `PullbackCoherence`. Its oplax
tensorator is the comparison of Tag 03EL and its oplax unit is `ν`, by construction. -/
def coreMonoidal (hf : PullbackCoherence f) : f.pullbackModules.CoreMonoidal :=
  Functor.CoreMonoidal.mk'
    (εIso := (pullbackUnitComparison f).symm)
    (μIso := fun F G ↦ (pullbackTensorComparisonIso f F G).symm)
    (μIso_inv_natural_left := fun v G ↦ pullbackTensorComparison_naturality_left f v G)
    (μIso_inv_natural_right := fun F u ↦ pullbackTensorComparison_naturality_right f F u)
    (oplax_associativity := fun F G H ↦ (hf.associativity F G H).symm)
    (oplax_left_unitality := fun F ↦ by
      rw [← cancel_mono (λ_ (f.pullbackModules.obj F)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, pullbackTensorComparisonIso_hom]
      rw [← hf.leftUnitality, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id])
    (oplax_right_unitality := fun F ↦ by
      rw [← cancel_mono (ρ_ (f.pullbackModules.obj F)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, pullbackTensorComparisonIso_hom]
      rw [← hf.rightUnitality, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id])

/-- The monoidal functor structure on the pullback, given the coherence. Deliberately **not** an
instance: the strict monoidal structure of Tag 01CA is itself not an instance, and this file
registers no monoidal pairing on a category which already has one. -/
@[instance_reducible]
def monoidal (hf : PullbackCoherence f) : f.pullbackModules.Monoidal :=
  (coreMonoidal f hf).toMonoidal

/-- The oplax tensorator of `monoidal` is the comparison of Tag 03EL, by construction. -/
theorem delta_monoidal (hf : PullbackCoherence f)
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Functor.OplaxMonoidal.δ (self := (monoidal f hf).toOplaxMonoidal) f.pullbackModules F G =
      pullbackTensorComparison f F G :=
  rfl

/-- The lax unit of `monoidal` is the inverse of `ν : f^*O_D ≅ O_C`, by construction. -/
theorem epsilon_monoidal (hf : PullbackCoherence f) :
    Functor.LaxMonoidal.ε (self := (monoidal f hf).toLaxMonoidal) f.pullbackModules =
      (pullbackUnitComparison f).inv :=
  rfl

/-- **The pushforward of sheaves of modules along a morphism of ringed topoi is lax monoidal,
given the coherence**: it is right adjoint to the pullback by Tag 03D7, so
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal` turns the oplax structure of `monoidal` into
a lax one. Its tensorator is therefore the mate of
`f^*(f_*M ⊗ f_*N) --δ--> f^*f_*M ⊗ f^*f_*N --ε ⊗ ε--> M ⊗ N`. -/
@[instance_reducible]
def pushforwardLaxMonoidal (hf : PullbackCoherence f) : (pushforwardModules f).LaxMonoidal :=
  letI := monoidal f hf
  (pullbackAdjPushforwardModules f).rightAdjointLaxMonoidal

end Comparisons

end Stacks.SheafOfModules.RingedToposPullback

end
