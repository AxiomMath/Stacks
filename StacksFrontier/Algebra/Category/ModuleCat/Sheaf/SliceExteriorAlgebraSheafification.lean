module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraSliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebraPresheafComparison

/-!
# The restriction of an exterior algebra to a slice site is an exterior algebra

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `M` a sheaf of modules over the
underlying sheaf of rings, `A` a sheaf of graded algebras with a degree-one generator
`gen : M ⟶ A¹` making it the exterior algebra of `M`, and `U : C`. This file proves that the
restriction `A|_U` to the slice site at `U` is the exterior algebra of `M|_U` on the restricted
generator.

## Why this is wanted

It is the hypothesis `hAV` of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`, the gluing
primitive for the local-to-global step of [Stacks, Tag 0BQY]: a homomorphism out of an exterior
algebra is an isomorphism in every degree as soon as both algebras restrict to exterior algebras
over the members of a cover.

The restriction of the chosen exterior algebra — `SheafOfModules.sectionwiseExteriorAlgebra`, the
degreewise sheafification of the sectionwise one — is *not presented* as a sheafification, so
`Stacks.GradedAlgebra.isExteriorAlgebra_sheafify` does not apply to it. What does apply is
`Stacks.GradedAlgebra.isUniversal_of_locallyBijective`, which carries a universal property to any
sheaf of graded algebras receiving a degreewise locally bijective multiplicative unital morphism
from a graded algebra of presheaves of modules. Such a morphism out of the slice site's *own*
sectionwise exterior algebra is built here.

## Main definitions

* `Stacks.SheafOfModules.SliceExterior.sliceExtAlg`: the slice site's own sectionwise exterior
  algebra of the restricted sections of `M`.
* `Stacks.SheafOfModules.SliceExterior.sliceUnit`: **the degreewise morphism into the restricted
  algebra** — `Stacks.SheafOfModules.SliceExterior.extendExtPowOver` followed by
  `Stacks.SheafOfModules.SliceSheafification.restrictedUnit`.
* `Stacks.SheafOfModules.SliceExterior.sliceDesc` and `sliceGen`: the unital homomorphism
  `sliceUnit` determines out of the sheafification, and the sheafified degree-one generator.
* `Stacks.SheafOfModules.SliceExterior.sliceSectionsIso`: `SheafOfModules.sheafifySectionsIso` on
  the slice site, with the ring sheaf spelled `(toRingCat J O♯)|_U`.

## Main results

* `Stacks.SheafOfModules.SliceExterior.sliceUnit_mul`, `sliceUnit_one`,
  `isLocallyInjective_sliceUnit` and `isLocallySurjective_sliceUnit`: **`sliceUnit` is
  multiplicative, unital and degreewise locally bijective.**
* `Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_over_sliceGen`: **the restriction of the
  chosen exterior algebra is an exterior algebra** of the sheafification over the slice site of
  the restricted sections.
* `Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_over`: **the restriction of an arbitrary
  exterior algebra of `M` is an exterior algebra of `M|_U`, on the restricted generator.**

## Implementation notes

**One spelling for the slice ring sheaf, chosen per statement.** The slice site's ring sheaf has
two descriptions, `(toRingCat J O♯)|_U` and `toRingCat (J.over U) (O♯|_U)`, which differ by the
associativity of `⋙`. They are definitionally equal and a single tolerant defeq test settles
them, but neither typeclass synthesis nor `rw` will cross between them, so each statement here is
written in the spelling its proof needs and the crossing is made exactly once, by `exact`:

* `isLocallyInjective_sliceUnit` and `isLocallySurjective_sliceUnit` are stated with the ring
  presheaf written `(Over.forget U).op ⋙ O♯ ⋙ forget₂ _ _`, because that is the spelling in
  which `Stacks.SheafOfModules.SliceExterior.isIso_toPresheaf_map_extendExtPowOver` is an
  instance; `Stacks.GradedAlgebra.isUniversal_of_locallyBijective` takes them as explicit
  arguments, which is where the crossing happens.
* `isExteriorAlgebra_sheafify_sliceExtAlg` and `sliceSectionsIso` restate
  `SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra` and
  `SheafOfModules.sheafifySectionsIso` in the `(toRingCat J O♯)|_U` spelling, once each.
  Restating them is what keeps the rest cheap: used inline, the first makes
  `SheafOfModules.GradedAlgebra.SquareZero.compUnitalHom` exhaust the heartbeat budget and the
  second makes `CategoryTheory.Iso.inv_hom_id_assoc` fail to match, its single pattern variable
  being unable to stand for two spellings of one category at once.

**`O♯` is supplied by name on the slice.** `SheafOfModules.sheafifySectionsIso` leaves its sheaf
of commutative rings implicit; inferring it at `M|_U` poses `?O♯'.obj ⋙ forget₂ _ _ =?=
(Over.forget U).op ⋙ (O♯.obj ⋙ forget₂ _ _)`, higher-order unification which exhausts the
budget. The same holds for the implicit `O` of `PresheafOfModules.extPowGen` at the slice. Both
are named.

**No `@[stacks]` attribute.** Nothing here is a clause of Tag 0BQY, whose statement is about the
comparison `⋀ⁱ(Ext¹) ⟶ Extⁱ`; this is the hypothesis about the *source* of that comparison which
its gluing step consumes. The 0BQY caveats in
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorLocal` record the state.
Tag 01CG's covering set is `SheafOfModules.exteriorPower_isSheafification` and its symmetric
companion, and this is not a clause of it either.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules
  Stacks.SheafOfModules.SliceSheafification

universe v u w

namespace Stacks.SheafOfModules.SliceExterior

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (M : _root_.SheafOfModules.{w} (toRingCat J Osharp))

/-- The slice site's own sectionwise exterior algebra of the restriction of the sections of
`M`. -/
abbrev sliceExtAlg : Stacks.GradedAlgebra (sliceExtPowFamily U M.val) :=
  (PresheafOfModules.extPowGradedAlgebra (O := (Over.forget U).op ⋙ Osharp.obj)
    ((sliceRestrict U (O := Osharp.obj)).obj M.val)).extend

/-- **The multiplicative unital morphism from the slice site's own sectionwise exterior algebra
to the restriction of the exterior algebra of `M`**: the comparison of the sectionwise exterior
powers followed by the restricted sheafification unit. -/
def sliceUnit (n : ℤ) :
    sliceExtPowFamily U M.val n ⟶
      (_root_.SheafOfModules.forget ((toRingCat J Osharp).over U) ⋙
        restrictScalars (𝟙 ((toRingCat J Osharp).over U).obj)).obj
          (((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).over
            U).piece n) :=
  extendExtPowOver U M.val n ≫
    restrictedUnit.{w} (toRingCat J Osharp) U
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n)

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The value of `Stacks.SheafOfModules.SliceExterior.sliceUnit` on a local section: the
comparison followed by the sheafification unit over the underlying object. -/
theorem sliceUnit_app (n : ℤ) (V : (Over U)ᵒᵖ)
    (x : (sliceExtPowFamily U M.val n).obj V) :
    PresheafOfModules.Hom.app (sliceUnit U M n) V x =
      PresheafOfModules.Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n)) (op V.unop.left)
        (PresheafOfModules.Hom.app (extendExtPowOver U M.val n) V x) := rfl

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **`sliceUnit` is multiplicative on homogeneous local sections.** -/
theorem sliceUnit_mul (i j : ℤ) (V : (Over U)ᵒᵖ)
    (x : (sliceExtPowFamily U M.val i).obj V) (y : (sliceExtPowFamily U M.val j).obj V) :
    PresheafOfModules.Hom.app (sliceUnit U M (i + j)) V
        (((sliceExtAlg U M).mul i j).app V x y) =
      (((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).over U).mul
          i j).app V (PresheafOfModules.Hom.app (sliceUnit U M i) V x)
        (PresheafOfModules.Hom.app (sliceUnit U M j) V y) :=
  (congrArg (fun z => PresheafOfModules.Hom.app
        (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) (i + j)))
        (op V.unop.left) z)
      (extendExtPowOver_mul U M.val i j V x y)).trans
    ((PresheafOfModules.extPowGradedAlgebra M.val).extend.sheafify_mul_unit
      (𝟙 (toRingCat J Osharp).obj) i j (op V.unop.left) _ _).symm

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **`sliceUnit` carries the degree-zero unit to the degree-zero unit.** -/
theorem sliceUnit_one (V : (Over U)ᵒᵖ) :
    PresheafOfModules.Hom.app (sliceUnit U M 0) V ((sliceExtAlg U M).one.eval V) =
      ((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).over
        U).one.eval V :=
  (congrArg (fun z => PresheafOfModules.Hom.app
        (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) 0)) (op V.unop.left) z)
      (extendExtPowOver_one U M.val V)).trans
    ((PresheafOfModules.extPowGradedAlgebra M.val).extend.sheafify_one_eval
      (𝟙 (toRingCat J Osharp).obj) (op V.unop.left)).symm

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- `sliceUnit` is the comparison followed by the restricted sheafification unit, at the level of
the underlying presheaves of abelian groups. -/
theorem toPresheaf_map_sliceUnit (n : ℤ) :
    (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
          forget₂ CommRingCat.{w} RingCat.{w})).map (sliceUnit U M n) =
      (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
            forget₂ CommRingCat.{w} RingCat.{w})).map (extendExtPowOver U M.val n) ≫
        overToSheafify.{w} (toRingCat J Osharp) U
          (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n) :=
  (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
    forget₂ CommRingCat.{w} RingCat.{w})).map_comp _ _

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **`sliceUnit` is locally injective in every degree**: the comparison is an isomorphism and
the restricted sheafification unit is locally injective.

The two factors' local injectivity is passed to `CategoryTheory.Presheaf.isLocallyInjective_comp`
positionally rather than by instance synthesis. Synthesis does not find them: the hypothesis in
the context and the instance goal have the same morphism but the `ConcreteCategory` arguments of
the class are synthesized afresh at each site, and resolution then fails on two instances that
print identically. This is the same obstruction that
`Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm` takes its
hypotheses explicitly to avoid. -/
theorem isLocallyInjective_sliceUnit (n : ℤ) :
    Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
        forget₂ CommRingCat.{w} RingCat.{w})).map (sliceUnit U M n)) := by
  have key := @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ (J.over U) _ _ _
    ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
      forget₂ CommRingCat.{w} RingCat.{w})).map (extendExtPowOver U M.val n))
    (overToSheafify.{w} (toRingCat J Osharp) U
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n))
    inferInstance
    (isLocallyInjective_overToSheafify.{w} (toRingCat J Osharp) U
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n))
  rwa [toPresheaf_map_sliceUnit]

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **`sliceUnit` is locally surjective in every degree.** See
`Stacks.SheafOfModules.SliceExterior.isLocallyInjective_sliceUnit` for why the two factors are
supplied positionally. -/
theorem isLocallySurjective_sliceUnit (n : ℤ) :
    Presheaf.IsLocallySurjective (J.over U)
      ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
        forget₂ CommRingCat.{w} RingCat.{w})).map (sliceUnit U M n)) := by
  have key := @Presheaf.isLocallySurjective_comp _ _ (J.over U) _ _ _ _ _ _ _ _ _
    ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ Osharp.obj ⋙
      forget₂ CommRingCat.{w} RingCat.{w})).map (extendExtPowOver U M.val n))
    (overToSheafify.{w} (toRingCat J Osharp) U
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n))
    inferInstance
    (isLocallySurjective_overToSheafify.{w} (toRingCat J Osharp) U
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k M.val) n))
  rwa [toPresheaf_map_sliceUnit]

/-- The degree-one generator of the sheafification over the slice site of the slice site's own
sectionwise exterior algebra. -/
abbrev sliceGen : (PresheafOfModules.sheafification (𝟙 ((toRingCat J Osharp).over U).obj)).obj
      ((sliceRestrict U (O := Osharp.obj)).obj M.val) ⟶
    ((sliceExtAlg U M).sheafify (𝟙 ((toRingCat J Osharp).over U).obj)).piece 1 :=
  (sliceExtAlg U M).sheafifyGen (𝟙 ((toRingCat J Osharp).over U).obj)
    (PresheafOfModules.extPowGen (O := (Over.forget U).op ⋙ Osharp.obj)
      ((sliceRestrict U (O := Osharp.obj)).obj M.val))

/-- **The unital homomorphism from the slice site's own exterior algebra to the restriction of
the exterior algebra of `M`** determined by `Stacks.SheafOfModules.SliceExterior.sliceUnit`. -/
def sliceDesc : _root_.SheafOfModules.GradedAlgebra.UnitalHom
    ((sliceExtAlg U M).sheafify (𝟙 ((toRingCat J Osharp).over U).obj))
    ((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).over U) :=
  (sliceExtAlg U M).descUnitalHom (𝟙 ((toRingCat J Osharp).over U).obj) (sliceUnit U M)
    (sliceUnit_mul U M) (sliceUnit_one U M)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The slice site's own sectionwise exterior algebra, sheafified over the slice site, is the
exterior algebra of the sheafification of the restricted sections.** This is
`SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra` on the site `(Over U, J.over U)`,
restated in the spelling of this file: its sheaf of rings is `(O♯|_U)` while the one here is
`(toRingCat J O♯)|_U`, the two differing by the associativity of `⋙`. -/
theorem isExteriorAlgebra_sheafify_sliceExtAlg :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      ((sliceExtAlg U M).sheafify (𝟙 ((toRingCat J Osharp).over U).obj)) (sliceGen U M) :=
  _root_.SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra (J.over U)
    (𝟙 (Osharp.over U).obj) ((M.over U).val)

/-- **The restriction to the slice site at `U` of the exterior algebra of `M` is an exterior
algebra** of the sheafification over the slice site of the restricted sections of `M`.

The slice site's own sectionwise exterior algebra is universal there
(`Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_sheafify_sliceExtAlg`), and
`Stacks.SheafOfModules.SliceExterior.sliceUnit` carries that universal property to the restricted
algebra by `Stacks.GradedAlgebra.isUniversal_of_locallyBijective`: it is multiplicative, unital
and degreewise locally bijective. The restricted algebra is not *presented* as a sheafification,
which is why `Stacks.GradedAlgebra.isExteriorAlgebra_sheafify` does not reach it. -/
theorem isExteriorAlgebra_over_sliceGen :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      ((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).over U)
      (sliceGen U M ≫ (sliceDesc U M).app 1) := by
  have hA := isExteriorAlgebra_sheafify_sliceExtAlg U M
  exact (sliceExtAlg U M).isUniversal_of_locallyBijective
    (Pr := fun _ κ => _root_.SheafOfModules.GradedAlgebra.SquareZero κ)
    (𝟙 ((toRingCat J Osharp).over U).obj) (sliceUnit U M) (sliceUnit_mul U M) (sliceUnit_one U M)
    (isLocallyInjective_sliceUnit U M) (isLocallySurjective_sliceUnit U M)
    (PresheafOfModules.extPowGen (O := (Over.forget U).op ⋙ Osharp.obj)
      ((sliceRestrict U (O := Osharp.obj)).obj M.val))
    hA (hA.1.compUnitalHom (sliceDesc U M))

/-- **Sheafifying over the slice site the restricted sections of `M` returns `M|_U`.** This is
`SheafOfModules.sheafifySectionsIso` on the site `(Over U, J.over U)`, with the ring sheaf
spelled `(toRingCat J O♯)|_U` rather than `toRingCat (J.over U) (O♯|_U)`.

The spelling is not cosmetic. The two differ by the associativity of `⋙`, so the two categories
of sheaves of modules carry different `Category` instances, and a composite of a morphism in one
with a morphism in the other is not matched by `CategoryTheory.Iso.inv_hom_id_assoc`: its single
pattern variable cannot be both. With the type ascribed here every composite below lives in one
category. -/
def sliceSectionsIso :
    (PresheafOfModules.sheafification (𝟙 ((toRingCat J Osharp).over U).obj)).obj
        ((sliceRestrict U (O := Osharp.obj)).obj M.val) ≅ M.over U :=
  _root_.SheafOfModules.sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- `Stacks.SheafOfModules.SliceExterior.sliceSectionsIso` undoes the sheafification unit on a
local section. -/
theorem sliceSectionsIso_hom_unit (V : (Over U)ᵒᵖ)
    (m : ((sliceRestrict U (O := Osharp.obj)).obj M.val).obj V) :
    (sliceSectionsIso U M).hom.val.app V
        (PresheafOfModules.Hom.app (sheafifyUnit (𝟙 ((toRingCat J Osharp).over U).obj)
          ((sliceRestrict U (O := Osharp.obj)).obj M.val)) V m) = m :=
  _root_.SheafOfModules.sheafifySectionsIso_hom_unit (J := J.over U) (Osharp := Osharp.over U)
    (M.over U) V m

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp))
  (gen : M ⟶ A.piece 1)
  (hgen : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)

include hgen

/-- **The generator transported onto `A.over U` is the restricted generator of `A`.** Both sides
are morphisms out of the sheafification over the slice site of the restricted sections of `M`, so
they agree as soon as they agree on the unit image of a local section; there both are
`gen` read over the underlying object.

The unit image of `m` goes to the unit image of `Λ¹m` by
`Stacks.GradedAlgebra.sheafifyGen_unit`, then to `sliceUnit` of `Λ¹m` by
`Stacks.GradedAlgebra.descUnitalHom_unit`, which is the unit image of `Λ¹m` for the *unsliced*
family over `op V.unop.left` — the comparison and the degree-one generator both being the
identity on sections — and that is the unit-image description of the generator of the unsliced
algebra (`sheafifyGen_unit` again), which `SheafOfModules.exteriorDesc_gen` carries to `gen`. On
the other side `SheafOfModules.sheafifySectionsIso_hom_unit` undoes the unit. -/
theorem sliceGen_comp_exteriorDesc_over :
    (sliceGen U M ≫ (sliceDesc U M).app 1) ≫
        ((_root_.SheafOfModules.exteriorDesc M A gen hgen).over U).app 1 =
      (sliceSectionsIso U M).hom ≫
        _root_.SheafOfModules.GradedAlgebra.genOver gen U := by
  refine PresheafOfModules.sheafification_hom_ext_apply
    (𝟙 ((toRingCat J Osharp).over U).obj) fun V m => ?_
  have h1 := (sliceExtAlg U M).sheafifyGen_unit (𝟙 ((toRingCat J Osharp).over U).obj)
    (PresheafOfModules.extPowGen (O := (Over.forget U).op ⋙ Osharp.obj)
      ((sliceRestrict U (O := Osharp.obj)).obj M.val)) V m
  have h2 := (sliceExtAlg U M).descUnitalHom_unit (𝟙 ((toRingCat J Osharp).over U).obj)
    (sliceUnit U M) (sliceUnit_mul U M) (sliceUnit_one U M) 1 V
    (PresheafOfModules.Hom.app (PresheafOfModules.extPowGen
      (O := (Over.forget U).op ⋙ Osharp.obj)
      ((sliceRestrict U (O := Osharp.obj)).obj M.val)) V m)
  have h4 := (PresheafOfModules.extPowGradedAlgebra M.val).extend.sheafifyGen_unit
    (toRingCatMap J (𝟙 Osharp.obj)) (PresheafOfModules.extPowGen M.val) (op V.unop.left) m
  have h5 := _root_.SheafOfModules.exteriorDesc_gen M A gen hgen (op V.unop.left) m
  have h6 := sliceSectionsIso_hom_unit U M V m
  refine Eq.trans (congrArg (fun z =>
    (((_root_.SheafOfModules.exteriorDesc M A gen hgen).over U).app 1).val.app V
      (((sliceDesc U M).app 1).val.app V z)) h1) ?_
  refine (congrArg _ (h2.trans h4.symm)).trans ?_
  exact h5.trans (congrArg (fun z => gen.val.app (op V.unop.left) z) h6.symm)

/-- **The restriction to a slice site of an exterior algebra of a sheaf of modules is an exterior
algebra of the restricted sheaf of modules, on the restricted generator.** This is what the
gluing step of [Stacks, Tag 0BQY] asks of the source of its comparison map over each member of
the cover: the hypothesis `hAV` of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`.

The restriction of the *chosen* exterior algebra — the sheafified sectionwise one — is an
exterior algebra by `Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_over_sliceGen`, and
`SheafOfModules.exteriorDesc` restricted to the slice site moves that across to `A.over U`:
restriction preserves unital homomorphisms and invertibility of each component
(`SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`), and
`Stacks.SheafOfModules.SliceExterior.sliceGen_comp_exteriorDesc_over` identifies the generator so
transported with `genOver gen U` precomposed with
`SheafOfModules.sheafifySectionsIso` on the slice site, which
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` then removes. -/
theorem isExteriorAlgebra_over :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra (A.over U)
      (_root_.SheafOfModules.GradedAlgebra.genOver gen U) := by
  have : ∀ n : ℤ, IsIso
      (((_root_.SheafOfModules.exteriorDesc M A gen hgen).over U).app n) := fun n => by
    have h : IsIso ((_root_.SheafOfModules.exteriorDesc M A gen hgen).app n) :=
      (_root_.SheafOfModules.exteriorPieceIso M A gen hgen n).isIso_hom
    exact (_root_.SheafOfModules.overFunctor.{w} (toRingCat J Osharp) U).map_isIso _
  have heq := sliceGen_comp_exteriorDesc_over U M A gen hgen
  have hsq : _root_.SheafOfModules.GradedAlgebra.SquareZero
      ((sliceGen U M ≫ (sliceDesc U M).app 1) ≫
        ((_root_.SheafOfModules.exteriorDesc M A gen hgen).over U).app 1) := by
    rw [heq]
    exact _root_.SheafOfModules.GradedAlgebra.squareZero_comp _ (hgen.1.over U)
  have key := (isExteriorAlgebra_over_sliceGen U M).ofDegreewiseIso
    ((_root_.SheafOfModules.exteriorDesc M A gen hgen).over U) hsq
  rw [heq] at key
  have h2 := _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso key
    (sliceSectionsIso U M).inv (sliceSectionsIso U M).symm.isIso_hom
  rwa [Iso.inv_hom_id_assoc] at h2

end Sheafify

end Stacks.SheafOfModules.SliceExterior

end
