module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associativity coherence of the total tensor comparison of a pullback, on a ringed topos

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi.  The comparison

`f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`

of total tensor complexes assembled from [Stacks, Tag 03EL] is compatible with the associator of
the monoidal structure on cochain complexes given by the total tensor product.  This file states
that compatibility, unconditionally, in two forms: for a morphism of ringed topoi in the
four-field presentation of [Stacks, Tag 03D6], and for a morphism presented by a functor of the
underlying sites which is a morphism of sites.

It is the ringed-topoi form of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator`, which says the
same for a morphism of ringed spaces.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.idCoreMonoidalSheafTensorToStrict`: the monoidal data of the
  identity functor of `Mod(O)` from the monoidal structure whose tensor product is
  `Stacks.SheafOfModules.Tensor.sheafTensor` to the strict structure of [Stacks, Tag 01CA], with
  the identity as its tensorator and as its unit comparison.
* `Stacks.Sheaves.DerivedPullback.pullbackModulesMonoidalSheafTensor`: **`f^*` is a monoidal
  functor for the monoidal structure whose tensor product is
  `Stacks.SheafOfModules.Tensor.sheafTensor`**, with the comparison of [Stacks, Tag 03EL] as its
  oplax tensorator.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalMu`: the inverse comparison at a pair of
  complexes, with its source read at the monoidal spelling `⊗` of the total tensor product rather
  than at `HomologicalComplex.mapBifunctor`.
* `Stacks.Sheaves.DerivedPullback.totalObj`, `complexAssociatorPairTopos`,
  `totalComplexMapRightTopos` and `totalComplexMapLeftTopos`: the total tensor complex, the
  associator of total tensor complexes, and the total tensor complex of a cochain map in one
  variable and an identity in the other, all read at the `HomologicalComplex.mapBifunctor`
  spelling.
* `Stacks.Sheaves.DerivedPullback.pullbackComplexMonoidalTopos`: the degreewise pullback along a
  site-presented morphism, as a monoidal functor on cochain complexes.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_associator`: **the associativity
  coherence of the comparison of total tensor complexes for a morphism of ringed topoi in the
  four-field presentation**, with no hypothesis.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_associator_pair`: **the same
  coherence for a site-presented morphism of ringed topoi**, written in the forward direction and
  at the `HomologicalComplex.mapBifunctor` spelling of the total tensor complex.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_eq_tensorator`: the comparison at a pair
  of complexes is the inverse tensorator of the monoidal lift of `f^*` to complexes;
  `delta_pullbackModules`, `delta_pullbackComplexFunctor` and `delta_pullbackComplex` are the
  same identification read on the oplax tensorator, at the sheaf level and at the complex level
  for each of the two presentations.

## Implementation notes

**No total complex is taken apart here.**  The comparison at a pair of complexes is the inverse
tensorator of the monoidal lift of `f^*` to complexes
(`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_eq_tensorator`), so the coherence is the
associativity clause of `CategoryTheory.Functor.Monoidal` for that lift —
`CategoryTheory.Functor.mapHomologicalComplexTensorator_associativity` in the `⊗` form and
`CategoryTheory.Functor.OplaxMonoidal.oplax_associativity` in the forward form.  That clause is
where the summandwise computation with the antidiagonal inclusions happens, and it is already
proved.  The only computation carried out here is the identification itself, on one summand:
`Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom` and
`CategoryTheory.Functor.ι_mapHomologicalComplexTensorator_hom` both name the comparison of
[Stacks, Tag 03EL] there, and `hom_ext_pullbackTotal` is the extensionality that reduces to it.

**Two monoidal structures on `Mod(O)`, and why the identity functor appears.**  The total tensor
complex and the K-flatness predicate of [Stacks, Tag 06Y9] are stated against the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor O`, so the monoidal structure the lift to complexes
must be taken over is `SheafOfModules.monoidalCategorySheafTensor`, whose curried tensor product
is that bifunctor on the nose.  `Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal` —
the monoidal structure on `f^*` carrying the comparison of [Stacks, Tag 03EL], unconditional by
`pullbackCoherence` — is stated instead at the strict structure of [Stacks, Tag 01CA].  The two
structures agree on objects, on the unit and on the associator by `rfl`, and on the two
whiskerings and the two unitors by the theorems of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree`; so the identity
functor between them is monoidal in both directions, and
`pullbackModulesMonoidalSheafTensor` is `pullbackMonoidal` conjugated by it.
`SheafOfModules.idMonoidalStrictToSheafTensor` serves on the target side.  On the source side the
existing `SheafOfModules.idMonoidalSheafTensorToStrict` is obtained as an adjoint mate, so its
tensorator is not the identity *definitionally*, and the identification of the conjugated
tensorator with the comparison of [Stacks, Tag 03EL] would not be available;
`idCoreMonoidalSheafTensorToStrict` is the same monoidal functor built with `Iso.refl` as its
tensorator, which makes `delta_pullbackModules` a one-line computation.

**Why `pullbackTensorTotalMu` and the four pinned names exist.**  The two spellings of the total
tensor complex — `HomologicalComplex.mapBifunctor` against
`Stacks.SheafOfModules.Tensor.sheafTensor`, which the type of
`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso` is written at, and `⊗` of
`CategoryTheory.MonoidalCategory`, which the associator and the tensorator are written at — are
the same object, but identifying them is a conversion check that the `HomologicalComplex`
instance arguments make expensive.  Each of `pullbackTensorTotalMu`,
`complexAssociatorPairTopos`, `totalComplexMapRightTopos` and `totalComplexMapLeftTopos` pays for
the identification **once**, in the ascribed type of a definition; the coherences are then
equations all of whose terms are at one spelling.  No heartbeat option is set.

**The transport to the site-presented pullback is the transport of the monoidal structure.**
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` is
`pullbackTensorTotalIso` for the four-field morphism of [Stacks, Tag 03D6] conjugated by the
identification `pullbackComplexSiteIso` of the two pullbacks of sheaves of modules, in each
tensor factor.  That is exactly the shape of `CategoryTheory.Functor.Monoidal.transport_δ`, so
`pullbackComplexMonoidalTopos` — the transport of the monoidal structure along the same
identification — has the transported comparison as its oplax tensorator
(`delta_pullbackComplex`), and the coherence for it is again a clause of
`CategoryTheory.Functor.OplaxMonoidal`.  No naturality square of the comparison is chased.

**Universes.**  Both statements are at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  That is the
layer `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` lives at, and it is also what
the monoidal structures force: `SheafOfModules.monoidalClosedSheafTensor`, which the total tensor
product of complexes needs in order to exist, is stated for a sheaf of rings in the universe
`max u v w` of the two site universes and the coefficient universe, and
`SheafOfModules.whiskerLeft_eq_strict` and its companions for one in `max u v`.
`pullbackTensorTotalIso` itself keeps the four universes of the two ringed topoi independent, and
nothing below identifies them beyond what those inputs ask for.

## What this is an input to

This is the **complex-level** coherence.  The derived-level statement — that the comparison of
[Stacks, Tag 07A4] carries the associativity constraint of the monoidal derived category of
[Stacks, Tag 0FPT] on `D(O')` to the one on `D(O)`, which is the coherence [Stacks, Tag 0FPL]
uses silently — is this together with two further inputs: the descent of a *three*-variable
identity along the localization by K-flat complexes with flat terms
(`Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat₃`), and the re-reading of the model
identification of [Stacks, Tag 07A4] against the second model of a triple tensor product.  The
three are fused by `CategoryTheory.bifunctor_comparison_assoc_of_bundles`, exactly as
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator` fuses the
ringed-space case.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Functor.LaxMonoidal Functor.OplaxMonoidal
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## The identity functor from the re-seated structure to the strict one -/

section Reseat

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u₀ v₀}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₀ v₀}]
  (R : Sheaf J CommRingCat.{max u₀ v₀})

/-- **The monoidal data of the identity functor of `Mod(O)` from the monoidal structure whose
tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor` to the strict structure of
[Stacks, Tag 01CA]**: the identity on tensor products and on units, which typechecks because the
two structures agree there on the nose, the coherence being exactly the agreement of the
associator, the two whiskerings and the two unitors
(`SheafOfModules.associator_eq_strict` and its companions).

It is the direction opposite to `SheafOfModules.idCoreMonoidalStrictToSheafTensor`, and it is
built with `Iso.refl` rather than as the mate of that one across the identity equivalence, so
that its tensorator is the identity definitionally. -/
def idCoreMonoidalSheafTensorToStrict :
    @Functor.CoreMonoidal _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R))
      (𝟭 (Stacks.SheafOfModules.Strict.Mod R)) :=
  letI : MonoidalCategory (Stacks.SheafOfModules.Strict.Mod R) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)
  have hwr : ∀ (A B W : Stacks.SheafOfModules.Strict.Mod R) (a : A ⊗ B ⟶ W),
      𝟙 A ▷ B ≫ 𝟙 (A ⊗ B) ≫ a = a := fun _ _ _ _ => by
    rw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.id_comp]
  have hwl : ∀ (A B W : Stacks.SheafOfModules.Strict.Mod R) (a : A ⊗ B ⟶ W),
      A ◁ 𝟙 B ≫ 𝟙 (A ⊗ B) ≫ a = a := fun _ _ _ _ => by
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
  have hwl' : ∀ (A B W : Stacks.SheafOfModules.Strict.Mod R) (b : W ⟶ A ⊗ B),
      b ≫ A ◁ 𝟙 B ≫ 𝟙 (A ⊗ B) = b := fun _ _ _ _ => by
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id]
  @Functor.CoreMonoidal.mk _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R))
    (𝟭 (Stacks.SheafOfModules.Strict.Mod R)) (Iso.refl _) (fun _ _ => Iso.refl _)
    (fun a X' => (Category.comp_id _).trans
      ((_root_.SheafOfModules.whiskerRight_eq_strict R a X').symm.trans
        (Category.id_comp _).symm))
    (fun X' a => (Category.comp_id _).trans
      ((_root_.SheafOfModules.whiskerLeft_eq_strict R X' a).symm.trans
        (Category.id_comp _).symm))
    (fun A B D => (hwr (A ⊗ B) D _ _).trans
      ((congrArg Iso.hom (_root_.SheafOfModules.associator_eq_strict R A B D)).trans
        (hwl' A (B ⊗ D) _ _).symm))
    (fun A => (congrArg Iso.hom (_root_.SheafOfModules.leftUnitor_eq_strict R A)).symm.trans
      (hwr _ A A _).symm)
    (fun A => (congrArg Iso.hom (_root_.SheafOfModules.rightUnitor_eq_strict R A)).symm.trans
      (hwl A _ A _).symm)

end Reseat

/-- Weak sheafification of abelian presheaves, from the global instance
`Stacks.SheafOfModules.coefficientSheafification`. It is made a local instance of high priority
so that the declarations below find it rather than the section variable
`[HasSheafify X.J AddCommGrpCat.{u}]`, and so do not depend on that variable. -/
private abbrev hasWeakSheafifyAddCommGrpCatAssociator (X : RingedTopos.{u, u, u}) :
    HasWeakSheafify X.J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCatAssociator

/- Since Lean v4.35.0 instance search reaches `HasWeakSheafify X.J AddCommGrpCat` through the
section variable `HasSheafify X.J AddCommGrpCat` (via `instHasWeakSheafifyOfHasSheafify`), which
would make that variable a hypothesis of the declarations below. With the bridge erased here, the
high-priority instance above is found instead, as before the bump. -/
attribute [-instance] instHasWeakSheafifyOfHasSheafify

/-! ## The monoidal structures on `Mod(O)` and on its cochain complexes -/

section Seating

variable (Z : RingedTopos.{u, u, u})
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The monoidal structure on `Mod(O)` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor O` and whose unit is `SheafOfModules.unit`.  This is the
structure the total tensor complex is stated at, and the one everything below is read at. -/
@[instance_reducible] local instance monoidalModules :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor Z.O

/-- The symmetry of that monoidal structure on `Mod(O)`. -/
@[instance_reducible] local instance symmetricModules :
    SymmetricCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor Z.O

/-- The tensor product of `Mod(O)` is bilinear on morphisms. -/
local instance monoidalPreadditiveModules :
    MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor Z.O

/-- `Mod(O)` is monoidal closed; this is what makes the tensor product commute with the
coproducts the total tensor complex is assembled from. -/
@[instance_reducible] local instance monoidalClosedModules :
    MonoidalClosed (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  _root_.SheafOfModules.monoidalClosedSheafTensor Z.O

/-- Two `ℤ`-graded objects of `Mod(O)` have a tensor product. -/
local instance hasTensorModules :
    ∀ A B : GradedObject ℤ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)),
      GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

/-- **The monoidal structure on cochain complexes of `O`-modules** given by the total tensor
product of the tensor double complex. -/
@[instance_reducible] local instance monoidalComplexes :
    MonoidalCategory
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :=
  HomologicalComplex.monoidalCategory _ _

variable
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]

/-- **The total tensor complex `Tot(K ⊗_O L)`** of two cochain complexes of `O`-modules, at the
`HomologicalComplex.mapBifunctor` spelling: this is the object the comparison of
[Stacks, Tag 03EL] on total complexes is stated at. -/
abbrev totalObj
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ :=
  HomologicalComplex.mapBifunctor K L
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)

/-- **The associator of total tensor complexes**, with its source and target written through
`Stacks.Sheaves.DerivedPullback.totalObj` rather than through `⊗`.

The two spellings of the total tensor complex are the same object, but the identification is a
conversion the `HomologicalComplex` instance arguments make expensive; this definition pays for it
**once**. -/
def complexAssociatorPairTopos
    (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    totalObj Z (totalObj Z K L) M ⟶ totalObj Z K (totalObj Z L M) :=
  (α_ K L M).hom

/-- **The total tensor complex of a cochain map and an identity in the second variable**, pinned
at the `Stacks.Sheaves.DerivedPullback.totalObj` spelling of its source and target. -/
def totalComplexMapRightTopos
    {A A' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ} (a : A ⟶ A')
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    totalObj Z A B ⟶ totalObj Z A' B :=
  a ▷ B

/-- **The total tensor complex of an identity and a cochain map in the second variable**, pinned;
the companion of `Stacks.Sheaves.DerivedPullback.totalComplexMapRightTopos`. -/
def totalComplexMapLeftTopos
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    {B B' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ} (b : B ⟶ B') :
    totalObj Z A B ⟶ totalObj Z A B' :=
  A ◁ b

end Seating

/-! ## A morphism of ringed topoi in the four-field presentation -/

section ToposHom

attribute [local instance] monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The pullback of sheaves of modules along a morphism of ringed topoi is a monoidal functor
for the monoidal structure whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`.**

It is `Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`, which says the same for the
strict structure of [Stacks, Tag 01CA], conjugated on both sides by the identity functor between
the strict structure and this one — `idCoreMonoidalSheafTensorToStrict` on the source and
`SheafOfModules.idMonoidalStrictToSheafTensor` on the target.  No coherence diagram is checked
here, and the oplax tensorator is still the comparison of [Stacks, Tag 03EL]
(`delta_pullbackModules`). -/
@[instance_reducible,
  ega "IV 10.2.8" "more general"]
local instance pullbackModulesMonoidalSheafTensor :
    @Functor.Monoidal _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.O) f.pullbackModules :=
  @Functor.Monoidal.instComp _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.O) (𝟭 _) _
      (@Functor.CoreMonoidal.toMonoidal _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
          (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) _
        (idCoreMonoidalSheafTensorToStrict Y.O))
    (@Functor.Monoidal.instComp _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.O)
      f.pullbackModules (𝟭 _)
      (Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal f)
      (_root_.SheafOfModules.idMonoidalStrictToSheafTensor X.O))

omit [HasSheafify X.J AddCommGrpCat] [HasSheafify Y.J AddCommGrpCat] in
/-- **The oplax tensorator of the monoidal structure carried by `f^*` is the comparison
`f^*(F ⊗_{O'} G) ⟶ f^*F ⊗_O f^*G` of [Stacks, Tag 03EL].**  Both conjugating identity functors
have the identity as their tensorator, so the conjugation leaves the comparison untouched. -/
theorem delta_pullbackModules
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    δ f.pullbackModules F G =
      Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison f F G := by
  change (f.pullbackModules ⋙ 𝟭 _).map (𝟙 _) ≫
      (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison f F G ≫ 𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- **`f^*` preserves the coproducts occurring in the total complex of a double cochain complex
over `ℤ`**: those indexed by an antidiagonal `ComplexShape.π (up ℤ) (up ℤ) (up ℤ) ⁻¹' {n}`.

This is `Stacks.Sheaves.DerivedPullback.pullbackModules_preservesColimitsOfSizeZero` — `f^*` is a
left adjoint, by [Stacks, Tag 03D7] — read at the shape of one antidiagonal.  It is the hypothesis
of `CategoryTheory.Functor.mapHomologicalComplexTensorator`, so it is what makes the monoidal
structure transport to complexes at all. -/
local instance pullbackModules_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      f.pullbackModules :=
  letI := Stacks.Sheaves.DerivedPullback.pullbackModules_preservesColimitsOfSizeZero f
  inferInstance

variable
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

/-- **The comparison `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)` of total tensor complexes is the
inverse tensorator of the monoidal lift of `f^*` to complexes**, read on the forward direction.

Both are determined on the summands of the target, which is a coproduct on the nose; on the
summand indexed by `(p, q)` both are the comparison of [Stacks, Tag 03EL] at `(K^p, L^q)`
followed by the inclusion, by
`Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom` and
`CategoryTheory.Functor.ι_mapHomologicalComplexTensorator_hom`. -/
theorem pullbackTensorTotalIso_hom_eq
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackTensorTotalIso f K L).hom =
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).inv := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine hom_ext_pullbackTotal f K L n (fun p q hpq => ?_)
  have h : HomologicalComplex.ιMapBifunctor ((pullbackComplexFunctor f).obj K)
        ((pullbackComplexFunctor f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)
        p q n hpq ≫
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).hom.f n =
      μ f.pullbackModules (K.X p) (L.X q) ≫ f.pullbackModules.map
        (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
          p q n hpq) :=
    Functor.ι_mapHomologicalComplexTensorator_hom f.pullbackModules K L p q n hpq
  have hid : (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).hom.f n ≫
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).inv.f n =
      𝟙 ((HomologicalComplex.mapBifunctor ((pullbackComplexFunctor f).obj K)
        ((pullbackComplexFunctor f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ)).X n) :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).hom_inv_id
  have hmc : μ f.pullbackModules (K.X p) (L.X q) ≫
      (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (K.X p, L.X q) =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
        (((pullbackComplexFunctor f).obj K).X p)).obj
          (((pullbackComplexFunctor f).obj L).X q)) := by
    rw [show (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (K.X p, L.X q) =
        δ f.pullbackModules (K.X p) (L.X q) from
      (delta_pullbackModules f (K.X p) (L.X q)).symm]
    exact Functor.Monoidal.μ_δ f.pullbackModules (K.X p) (L.X q)
  rw [ι_pullbackTensorTotalIso_hom f K L p q n hpq,
    ← cancel_epi (μ f.pullbackModules (K.X p) (L.X q)), ← reassoc_of% h, hid, Category.comp_id,
    ← Category.assoc, hmc]
  exact Category.id_comp _

/-- **The comparison of total tensor complexes of [Stacks, Tag 03EL] is the inverse tensorator of
the monoidal lift of `f^*` to complexes**, as isomorphisms. -/
theorem pullbackTensorTotalIso_eq_tensorator
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorTotalIso f K L =
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).symm :=
  Iso.ext (pullbackTensorTotalIso_hom_eq f K L)

/-- **The comparison of total tensor complexes, read at the monoidal spelling of the total tensor
product.**  `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso` has its target written with
the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, while the associator and the tensorator
are written with `⊗`; the two are the same object, and this is the inverse comparison with the
second spelling ascribed, so that a statement combining it with the associator pays for the
identification once rather than once per occurrence. -/
def pullbackTensorTotalMu
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplexFunctor f).obj K ⊗ (pullbackComplexFunctor f).obj L ⟶
      (pullbackComplexFunctor f).obj (K ⊗ L) :=
  (pullbackTensorTotalIso f K L).inv

/-- **`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalMu` is the tensorator of the monoidal
lift of `f^*` to complexes.** -/
theorem pullbackTensorTotalMu_eq_tensorator
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorTotalMu f K L =
      (Functor.mapHomologicalComplexTensorator f.pullbackModules K L).hom :=
  congrArg Iso.inv (pullbackTensorTotalIso_eq_tensorator f K L)

/-- **The associativity coherence of the comparison of total tensor complexes on a ringed
topos.**  For cochain complexes `K, L, M` of `O'`-modules the square

```
(f^*K ⊗ f^*L) ⊗ f^*M ⟶ f^*Tot(K ⊗ L) ⊗ f^*M ⟶ f^*Tot(Tot(K ⊗ L) ⊗ M)
         |                                              |
         | α                                            | f^*α
         v                                              v
f^*K ⊗ (f^*L ⊗ f^*M) ⟶ f^*K ⊗ f^*Tot(L ⊗ M) ⟶ f^*Tot(K ⊗ Tot(L ⊗ M))
```

commutes, the unlabelled arrows being the comparison of [Stacks, Tag 03EL] assembled on total
complexes in one or the other tensor factor and `α` the associator of the total tensor product.
This is the associativity clause of `CategoryTheory.Functor.Monoidal` for the monoidal lift of
`f^*` to complexes, read through the identification of the comparison with the tensorator. -/
theorem pullbackTensorTotalIso_associator
    (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorTotalMu f K L ▷ (pullbackComplexFunctor f).obj M ≫
        pullbackTensorTotalMu f (K ⊗ L) M ≫
          (pullbackComplexFunctor f).map (α_ K L M).hom =
      (α_ ((pullbackComplexFunctor f).obj K) ((pullbackComplexFunctor f).obj L)
            ((pullbackComplexFunctor f).obj M)).hom ≫
        (pullbackComplexFunctor f).obj K ◁ pullbackTensorTotalMu f L M ≫
          pullbackTensorTotalMu f K (L ⊗ M) := by
  simp only [pullbackTensorTotalMu_eq_tensorator]
  exact Functor.mapHomologicalComplexTensorator_associativity f.pullbackModules K L M

/-- **The oplax tensorator of the monoidal lift of `f^*` to complexes is the comparison of total
tensor complexes**, in the forward direction. -/
theorem delta_pullbackComplexFunctor
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    δ (pullbackComplexFunctor f) K L = (pullbackTensorTotalIso f K L).hom :=
  (congrArg Iso.hom (pullbackTensorTotalIso_eq_tensorator f K L)).symm

end ToposHom

/-! ## A site-presented morphism of ringed topoi -/

section SiteMorphism

attribute [local instance] monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  pullbackModulesMonoidalSheafTensor pullbackModules_preservesAntidiagonalCoproducts

open Stacks.Sheaves.DerivedPullback.KFlatPullback

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
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The degreewise pullback of cochain complexes along a site-presented morphism of ringed
topoi is a monoidal functor** for the total tensor product.

It is the monoidal lift of `f^*` for the four-field morphism of [Stacks, Tag 03D6] attached to
the presentation, transported along the identification
`Stacks.Sheaves.DerivedPullback.pullbackComplexSiteIso` of the two pullbacks of cochain complexes
by `CategoryTheory.Functor.Monoidal.transport`.  It is not an instance: the
morphism-of-sites hypothesis does not appear in its type, so it cannot be synthesized. -/
@[instance_reducible] def pullbackComplexMonoidalTopos :
    (pullbackComplex f).Monoidal :=
  Functor.Monoidal.transport (pullbackComplexSiteIso f hmos)

/-- **The oplax tensorator of `Stacks.Sheaves.DerivedPullback.pullbackComplexMonoidalTopos` is
the comparison of total tensor complexes for the site-presented pullback.**  Both are the
comparison for the four-field morphism conjugated by the identification of the two pullbacks of
cochain complexes, in each tensor factor: for the tensorator that is
`CategoryTheory.Functor.Monoidal.transport_δ`, and for
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` it is its definition. -/
theorem delta_pullbackComplex
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    δ (self := (pullbackComplexMonoidalTopos f hmos).toOplaxMonoidal) (pullbackComplex f) K L =
      (pullbackToposTensorTotalIso f hmos K L).hom := by
  rw [show δ (self := (pullbackComplexMonoidalTopos f hmos).toOplaxMonoidal)
        (pullbackComplex f) K L =
      (pullbackComplexSiteIso f hmos).inv.app (K ⊗ L) ≫
        δ (pullbackComplexFunctor (modulesHomOfSiteHom f hmos)) K L ≫
          ((pullbackComplexSiteIso f hmos).hom.app K ⊗ₘ
            (pullbackComplexSiteIso f hmos).hom.app L)
      from Functor.Monoidal.transport_δ (pullbackComplexSiteIso f hmos) K L,
    delta_pullbackComplexFunctor (modulesHomOfSiteHom f hmos) K L]
  rfl

/-- **The associativity coherence of the comparison of total tensor complexes for a
site-presented morphism of ringed topoi**, in the forward direction and with every term written
at the `HomologicalComplex.mapBifunctor` spelling of the total tensor complex.

For cochain complexes `K, L, M` of `O'`-modules the square

```
f^*Tot(Tot(K ⊗ L) ⊗ M) ⟶ Tot(f^*Tot(K ⊗ L) ⊗ f^*M) ⟶ Tot(Tot(f^*K ⊗ f^*L) ⊗ f^*M)
         |                                                         |
         | f^*α                                                    | α
         v                                                         v
f^*Tot(K ⊗ Tot(L ⊗ M)) ⟶ Tot(f^*K ⊗ f^*Tot(L ⊗ M)) ⟶ Tot(f^*K ⊗ Tot(f^*L ⊗ f^*M))
```

commutes, the horizontal arrows being the comparison of [Stacks, Tag 03EL] on total complexes and
its assembly in one tensor factor, and `α` the associator of the total tensor product.  This is
the associativity clause of `CategoryTheory.Functor.OplaxMonoidal` for
`Stacks.Sheaves.DerivedPullback.pullbackComplexMonoidalTopos`, read through
`delta_pullbackComplex`; no total complex is taken apart and no naturality square is chased. -/
theorem pullbackToposTensorTotalIso_associator_pair
    (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackToposTensorTotalIso f hmos (totalObj Y K L) M).hom ≫
        totalComplexMapRightTopos X ((pullbackToposTensorTotalIso f hmos K L).hom)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPairTopos X ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) =
      (pullbackComplex f).map (complexAssociatorPairTopos Y K L M) ≫
        (pullbackToposTensorTotalIso f hmos K (totalObj Y L M)).hom ≫
          totalComplexMapLeftTopos X ((pullbackComplex f).obj K)
            ((pullbackToposTensorTotalIso f hmos L M).hom) := by
  simp only [← delta_pullbackComplex f hmos, totalComplexMapRightTopos, totalComplexMapLeftTopos,
    complexAssociatorPairTopos]
  exact Functor.OplaxMonoidal.oplax_associativity
    (self := (pullbackComplexMonoidalTopos f hmos).toOplaxMonoidal) (pullbackComplex f) K L M

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
