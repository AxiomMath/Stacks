module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.SheafVariableComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Homology.KFlat.BifunctorSingleBothFactors

/-!
# The degreewise tensor complex: the bifunctor spelling and the localized one

A complex `E` of `𝒪`-modules and a single `𝒪`-module `M` give a degreewise tensor product
`p ↦ Eᵖ ⊗_𝒪 M`, and the library builds it twice.

* `CochainComplex.KFlatBifunctor.rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor R) E M` has
  terms `((sheafTensor R).obj (E.X p)).obj M`, the sheafification of the sectionwise tensor
  product of the underlying presheaves. This is the spelling every K-flatness argument uses,
  because `rowComplex` is stated for an abstract bifunctor.
* `Stacks.SectionTensorFormula.tensorComplex E M` has terms `E.X p ⊗ M` and differentials
  `E.d p p' ▷ M` for `Stacks.SheafInternalHom.schemeMonoidalCategory`, the monoidal structure
  obtained by *localizing* the sectionwise one. This is the spelling the section formula
  `Stacks.SectionTensorFormula.sectionsTensorComplexIso` is stated in.

The localized monoidal product carries no formula, so the two are not the same complex and
nothing identified them. This file does, and the comparison is not degreewise-only: it is the
image under `Functor.mapHomologicalComplex` of a natural isomorphism of the two
one-variable tensor functors, so it is a chain map by construction rather than by a square
checked in each degree.

## Main definitions

* `Stacks.SheafOfModules.Tensor.sheafTensorFlipIsoTensorRight`: **`- ⊗_𝒪 M` computed by
  sheafification is `MonoidalCategory.tensorRight M` of the localized monoidal structure**, as
  functors on `Mod(𝒪)` over an arbitrary ringed site. This is
  `SheafOfModules.sheafTensorNatIso` read in the first variable.
* `Stacks.SheafOfModules.Tensor.rowComplexIsoTensorRightComplex`: **the comparison of complexes
  over an arbitrary ringed site**,
  `rowComplex (sheafTensor R) E M ≅ ((tensorRight M).mapHomologicalComplex _).obj E`.
* `Stacks.SectionTensorFormula.rowComplexIsoTensorComplex`: **the comparison at a scheme**,
  `rowComplex (sheafTensor X.sheaf) E M ≅ Stacks.SectionTensorFormula.tensorComplex E M`. This is
  the isomorphism that
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/CohomologyAffineAdicComparison.lean`
  records as missing from the Mittag-Leffler step of part (2) of [Stacks, Tag 0A0K].

## Main results

* `Stacks.SectionTensorFormula.tensorComplex_eq_mapHomologicalComplex`: **`tensorComplex` is
  `tensorRight M` applied degreewise**, by `rfl`. The localized monoidal structure on sheaves of
  modules *is* monoidally preadditive — `SheafOfModules.monoidalPreadditiveRingSheaf` is available,
  and so is `Stacks.SectionRingProjQuasicoherent.schemeMonoidalPreadditive` at the other
  spelling — so `Functor.mapHomologicalComplex` is available for it. It is the same complex, not
  an isomorphic one.
* `Stacks.SheafOfModules.Tensor.rowComplexIsoTensorRightComplex_hom_f` and
  `Stacks.SectionTensorFormula.rowComplexIsoTensorComplex_hom_f`: the comparison in each degree
  is `SheafOfModules.sheafTensorIso` at `E.X p`, so a consumer that has to compose it with the
  section formula never has to unfold `Functor.mapHomologicalComplex`.

## Implementation notes

**The bifunctor comparison already exists, and the two sides are closer than they
look.** `SheafOfModules.sheafTensorNatIso` identifies `curriedTensor (Mod(𝒪))` of the localized
structure with `Stacks.SheafOfModules.Tensor.sheafTensor R` as bifunctors; what is added here is
only its consequence on complexes. So nothing here re-derives the degreewise comparison from
`Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` and its first-variable naturality
`tensorSheafIsoTensorObj_hom_whiskerRight`, even though that route is also available: a second
account of the same identification is what this area already suffers from.

**Three spellings of one monoidal structure, and why no goal mentions two of them.**
`Stacks.SheafOfModules.monoidalCategory`, its reseating
`SheafOfModules.monoidalCategoryRingSheaf` at the `Stacks.SheafOfModules.Tensor.ringSheaf`
spelling of the sheaf of rings, and `Stacks.SheafInternalHom.schemeMonoidalCategory` all localize
the same sectionwise structure along the same sheafification and differ only in the chosen unit
object, so their tensor products and whiskerings are definitionally equal — see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/PowerCompareAgreement.lean`. A *goal*
mentioning two of them is not type-correct at the transparency `rw` and `simp` check their
motives at. Every step below is therefore a term, and each statement names one spelling only;
the one cross-spelling identification is `tensorComplex_eq_mapHomologicalComplex`, where `rfl`
checks it at default transparency.

**Universes.** The site-level statements are pinned to sections in `max u v` because
`SheafOfModules.sheafTensorNatIso` is: the monoidal structure on sheaves of modules is localized
through the internal hom of presheaves of modules. For a scheme the site is `X.Opens`, whose hom
universe is `0`, so the pin is vacuous and the scheme-level statements are at `.{u}`.

**Additivity of `⊗_𝒪` is carried as a hypothesis, as its consumers carry it.** `rowComplex` is
stated for an additive bifunctor, and `Stacks.SheafOfModules.Tensor.sheafTensor_additive` proves
that with no hypothesis — but instance search does not reach it, because the sections universe of
`sheafTensor` is `max u v` and search has to solve `max ?u ?v = u` over the site of a scheme. So
every statement here binds it, exactly as
`Stacks.Algebraization.derivedTensorSingleIsoRowComplex` and
`Stacks.SheafOfModules.rowComplexUnitIso` already do, and a consumer discharges it with
`letI := Stacks.SheafOfModules.Tensor.sheafTensor_additive X.sheaf`. The companion
`((sheafTensor R).flip.obj M).Additive` that
`CochainComplex.KFlatBifunctor.rowComplex_eq_mapHomologicalComplex` asks for is deduced here
from it, addition in a functor category being pointwise; the two monoidal instances named in the
scheme section are named for the same universe reason.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)

## What is not done

No project attribute is attached. The comparison is a statement about this repository's two
packagings of the degreewise tensor product, not a statement of the source.

Only the first tensor variable is treated. The mirror comparison for a complex in the *second*
variable, `rowComplex (sheafTensor R).flip` against `tensorLeft`, is not stated; nothing needs it
yet, and `SheafOfModules.sheafTensorNatIso` gives it by the same two lines.

The comparison is not transported to the derived category and is not compared with
`Stacks.Algebraization.derivedTensorSingleIsoRowComplex`, which is the statement that puts the
left-hand side here under `DerivedCategory.Q`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

universe v u

namespace Stacks.SheafOfModules.Tensor

/-! ### An arbitrary ringed site -/

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory

variable (M : SheafOfModules.{max u v} (ringSheaf R))

/-- **`- ⊗_𝒪 M` is additive**, for the sheafified sectionwise tensor product. The bifunctor
`⊗_𝒪` is additive in its first variable by
`Stacks.SheafOfModules.Tensor.sheafTensor_additive`, which is additivity as a functor into a
functor category; addition there is pointwise, so it specializes at `M`. This is the instance
`CochainComplex.KFlatBifunctor.rowComplex_eq_mapHomologicalComplex` asks for, and it is not
implied formally by additivity of the bifunctor — only by it together with the pointwise
description of addition. -/
instance sheafTensorFlipObj_additive [(sheafTensor.{u, v, max u v, max u v, max u v} R).Additive] :
    ((sheafTensor.{u, v, max u v, max u v, max u v} R).flip.obj M).Additive where
  map_add {_ _ f g} :=
    (NatTrans.congr_app
      ((sheafTensor.{u, v, max u v, max u v, max u v} R).map_add (f := f) (g := g)) M).trans
      (NatTrans.app_add M _ _)

/-- **Tensoring with a fixed `𝒪`-module: the sheafification formula is the localized functor.**
As functors on `Mod(𝒪)`, `F ↦ (F ⊗_{pre} M)^#` is `MonoidalCategory.tensorRight M` of the
monoidal structure obtained by localizing the sectionwise one.

This is `SheafOfModules.sheafTensorNatIso`, the identification of
`Stacks.SheafOfModules.Tensor.sheafTensor R` with `curriedTensor (Mod(𝒪))` as bifunctors, read in
the first variable: the components are its components at `M` and the squares are its naturality
in the first variable, applied at `M`. -/
def sheafTensorFlipIsoTensorRight :
    (sheafTensor.{u, v, max u v, max u v, max u v} R).flip.obj M ≅ MonoidalCategory.tensorRight M :=
  (NatIso.ofComponents (fun F => ((_root_.SheafOfModules.sheafTensorNatIso R).app F).app M)
    (fun {_ _} f => NatTrans.congr_app
      ((_root_.SheafOfModules.sheafTensorNatIso R).hom.naturality f) M)).symm

/-- The component of `sheafTensorFlipIsoTensorRight R M` at `F` is the inverse of
`SheafOfModules.sheafTensorIso R F M`. -/
@[simp]
lemma sheafTensorFlipIsoTensorRight_hom_app
    (F : SheafOfModules.{max u v} (ringSheaf R)) :
    (sheafTensorFlipIsoTensorRight R M).hom.app F =
      (_root_.SheafOfModules.sheafTensorIso R F M).inv :=
  rfl

variable [(sheafTensor.{u, v, max u v, max u v, max u v} R).Additive]

/-- **The degreewise tensor product of a complex with a fixed module: the bifunctor spelling is
the localized one.** For `E` a complex of `𝒪`-modules and `M` an `𝒪`-module,

`(p ↦ (Eᵖ ⊗_{pre} M)^#) ≅ (p ↦ Eᵖ ⊗ M)`,

the left-hand side being `CochainComplex.KFlatBifunctor.rowComplex` of the sheafified sectionwise
tensor product and the right-hand side `MonoidalCategory.tensorRight M` of the localized monoidal
structure applied degreewise.

Two steps, both available. `rowComplex F E M` is `F(-, M)` applied degreewise, by
`CochainComplex.KFlatBifunctor.rowComplex_eq_mapHomologicalComplex`; and `F(-, M)` is
`tensorRight M` by `sheafTensorFlipIsoTensorRight`. So the comparison is the image of a natural
isomorphism of functors under `Functor.mapHomologicalComplex`, which is why it is a chain map
with no square to check. -/
def rowComplexIsoTensorRightComplex
    (E : CochainComplex (SheafOfModules.{max u v} (ringSheaf R)) ℤ) :
    CochainComplex.KFlatBifunctor.rowComplex (sheafTensor.{u, v, max u v, max u v, max u v} R) E M ≅
      ((MonoidalCategory.tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  eqToIso (CochainComplex.KFlatBifunctor.rowComplex_eq_mapHomologicalComplex
      (sheafTensor.{u, v, max u v, max u v, max u v} R) E M) ≪≫
    (NatIso.mapHomologicalComplex (sheafTensorFlipIsoTensorRight R M)
      (ComplexShape.up ℤ)).app E

/-- **The comparison in each degree is `SheafOfModules.sheafTensorIso`.** Nothing of
`Functor.mapHomologicalComplex` survives in the components, so a consumer composing the
comparison with a formula on sections works degreewise against the identification of the
tensor product sheaf of [Stacks, Tag 01CA] with the localized monoidal product. -/
@[simp]
lemma rowComplexIsoTensorRightComplex_hom_f
    (E : CochainComplex (SheafOfModules.{max u v} (ringSheaf R)) ℤ) (p : ℤ) :
    (rowComplexIsoTensorRightComplex R M E).hom.f p =
      (_root_.SheafOfModules.sheafTensorIso R (E.X p) M).inv :=
  rfl

end Site

end Stacks.SheafOfModules.Tensor

namespace Stacks.SectionTensorFormula

/-! ### A scheme -/

section SchemeLevel

variable {X : Scheme.{u}} [(sheafTensor.{u, u, u, u, u} X.sheaf).Additive]

/-- The localized monoidal structure on the `𝒪_X`-modules of a scheme, at the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` of its sheaf of rings — the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor` is stated in. This is
`SheafOfModules.monoidalCategoryRingSheaf`, named rather than synthesized: its sections universe
is `max u v`, and over the site of a scheme instance search has to solve `max ?u ?v = u`, which
it does not. -/
local instance monoidalCategoryRingSheafScheme :
    MonoidalCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
  _root_.SheafOfModules.monoidalCategory X.sheaf

/-- **The localized tensor product of the `𝒪_X`-modules of a scheme is bilinear on morphisms**,
which is what makes `MonoidalCategory.tensorRight M` an additive functor and so puts
`Functor.mapHomologicalComplex` at its disposal. This is
`SheafOfModules.monoidalPreadditiveRingSheaf`, named for the same universe reason as
`monoidalCategoryRingSheafScheme`; `Stacks.SectionRingProjQuasicoherent.schemeMonoidalPreadditive`
is the same statement at the `AlgebraicGeometry.Scheme.Modules` spelling. -/
local instance monoidalPreadditiveRingSheafScheme :
    MonoidalPreadditive (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
  _root_.SheafOfModules.monoidalPreadditiveRingSheaf X.sheaf

omit [(sheafTensor.{u, u, u, u, u} X.sheaf).Additive] in
/-- **`Stacks.SectionTensorFormula.tensorComplex` is `MonoidalCategory.tensorRight` applied
degreewise**, and the two are the same complex rather than isomorphic ones.

`tensorComplex` proves its own `shape` and `d_comp_d'` from
`Stacks.SectionTensorFormula.zero_whiskerRight_modules`, without using additivity of the
localized monoidal structure on sheaves of modules. That additivity holds:
`SheafOfModules.monoidalPreadditiveRingSheaf` makes `tensorRight M` an additive functor, as does
`Stacks.SectionRingGeometric.schemeTensorRightAdditive` at the `AlgebraicGeometry.Scheme.Modules`
spelling, so `Functor.mapHomologicalComplex` applies to it and `tensorComplex` would have needed
no `d_comp_d'` of its own. This identification lets every lemma about the image of a complex
under an additive functor be used on it.

This is the one statement in the file whose two sides name different spellings of the monoidal
structure: `tensorComplex` is `Stacks.SheafInternalHom.schemeMonoidalCategory` and `tensorRight`
here is `SheafOfModules.monoidalCategoryRingSheaf`. They localize the same sectionwise structure
along the same sheafification, so `rfl` closes it at default transparency; no tactic that checks
a motive would. -/
theorem tensorComplex_eq_mapHomologicalComplex {κ : Type*} {c : ComplexShape κ}
    (E : HomologicalComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) c)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :
    tensorComplex E M = ((MonoidalCategory.tensorRight M).mapHomologicalComplex c).obj E :=
  rfl

/-- **The two degreewise tensor complexes of a scheme are isomorphic.** For `E` a complex of
`𝒪_X`-modules and `M` an `𝒪_X`-module,

`CochainComplex.KFlatBifunctor.rowComplex (sheafTensor X.sheaf) E M ≅
  Stacks.SectionTensorFormula.tensorComplex E M`.

The left-hand side has terms `(Eᵖ ⊗_{pre} M)^#`, the tensor product sheaf of [Stacks, Tag 01CA],
and is the complex the K-flatness machinery is stated in — it is the one appearing in
`Stacks.Algebraization.derivedTensorSingleIsoRowComplex`. The right-hand side has terms `Eᵖ ⊗ M`
for the localization of the sectionwise monoidal structure, which carries no formula, and is the
complex the affine section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` is stated in. Their identification is what
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/CohomologyAffineAdicComparison.lean`
records as the third of the three statements missing from the Mittag-Leffler step of part (2) of
[Stacks, Tag 0A0K].

No geometric hypothesis is used: not affineness of an open, not quasi-coherence of any term, and
not K-flatness of `E`. Only the additivity of `⊗_𝒪` in its first variable, which `rowComplex`
needs to exist at all and which `Stacks.SheafOfModules.Tensor.sheafTensor_additive` discharges. -/
def rowComplexIsoTensorComplex
    (E : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ℤ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :
    CochainComplex.KFlatBifunctor.rowComplex (sheafTensor.{u, u, u, u, u} X.sheaf) E M ≅
      tensorComplex E M :=
  Stacks.SheafOfModules.Tensor.rowComplexIsoTensorRightComplex X.sheaf M E ≪≫
    eqToIso (tensorComplex_eq_mapHomologicalComplex E M).symm

/-- **The comparison of the two degreewise tensor complexes is `SheafOfModules.sheafTensorIso` in
each degree**, so composing it with the affine section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` is a degreewise computation and no
consumer has to unfold `Functor.mapHomologicalComplex`. -/
@[simp]
lemma rowComplexIsoTensorComplex_hom_f
    (E : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ℤ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) (p : ℤ) :
    (rowComplexIsoTensorComplex E M).hom.f p =
      (_root_.SheafOfModules.sheafTensorIso X.sheaf (E.X p) M).inv :=
  rfl

end SchemeLevel

end Stacks.SectionTensorFormula

end
