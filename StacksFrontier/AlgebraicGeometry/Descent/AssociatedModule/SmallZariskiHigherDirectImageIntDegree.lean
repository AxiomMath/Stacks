module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiHigherDirectImage

/-!
# The small Zariski higher direct images of an associated module, in an integer degree

Let `f : T ⟶ S` be a morphism of schemes of a big Zariski site and let `𝓕 ↦ 𝓕^a` be the
associated-module functor of [Stacks, Tag 03DU] (4) at `τ = Zariski`.  The Zariski comparison

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`

is proved in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiHigherDirectImage.lean` at a
degree `i : ℕ` cast into `ℤ`, which is the degree the base-change input
`StacksTag03LR.rightDerivedPlusBaseChangeIso` is indexed by.  This file restates it at a genuine
integer degree `i : ℤ`, which is how [Stacks, Tag 071N] reads it and the shape a statement of the
whole tag consumes.  Nothing is reproved: the nonnegative degrees are that isomorphism
transported along `i = i.toNat`, and the negative degrees are a vanishing statement.

## Main results

* `AlgebraicGeometry.SmallZariski.isZero_rightDerivedPlus_pushforward_associatedModule_of_neg`
  and `AlgebraicGeometry.SmallZariski.isZero_associatedModule_rightDerivedPlus_pushforward_of_neg`:
  both sides of the comparison vanish in every negative degree.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntIsoOfEq`: the
  `ℕ`-indexed comparison read at an integer degree `i` carrying a witness `i = n`.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntIsoOfNonneg`: **the
  comparison at an integer degree `0 ≤ i`**, as an isomorphism of functors.  This is the
  mathematical content of the file.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntIso`: the comparison at
  an *arbitrary* integer degree.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntObjIso` and
  `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntObjIso_naturality`: that
  comparison at a single module, and its naturality in the module.

## Implementation notes

**Which degrees carry content.**  `CategoryTheory.Functor.rightDerivedPlus` is defined at every
`i : ℤ`, but it is the `i`-th cohomology of the image of a complex concentrated in degree `0`, so
it vanishes for `i < 0`: this is `CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`.  Both
sides of the comparison are therefore zero below degree `0` — the right-hand side because
`𝓕 ↦ 𝓕^a` is additive and so carries a zero object to a zero object — and the comparison there is
the unique isomorphism between zero objects, carrying no information.  The transport from the
`ℕ`-indexed statement closes for `0 ≤ i` and only for `0 ≤ i`, which is what
`higherDirectImageAssociatedModulePlusIntIsoOfNonneg` states; the unrestricted
`higherDirectImageAssociatedModulePlusIntIso` is that isomorphism in nonnegative degrees and the
isomorphism of zero objects below, so it is a true statement at every `i : ℤ` with its content
concentrated in `i ≥ 0`.  Both are recorded, so that a consumer needing the comparison itself
cannot pick up the vacuous half by accident.

**No hypothesis is imposed on `f` or on `𝓕`.**  [Stacks, Tag 071N] states its comparison for a
quasi-compact quasi-separated `f` and a quasi-coherent `𝓕`, because the étale half needs both; the
Zariski half needs neither, for the reason recorded in the documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiHigherDirectImage.lean`.  No
such hypothesis is introduced here either, so these statements remain stronger than the tag asks
on this side.

The `HasDerivedCategory` instances needed to speak of `rightDerivedPlus` at all are left free, as
in the file being restated.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 05U4](https://stacks.math.columbia.edu/tag/05U4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w₁ w₂ w₃ w₄

-- The priority raise documented in
-- `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiHigherDirectImage.lean`:
-- with the module-universe-`max u v r w` instances in the import closure, instance search for
-- `Abelian` on the modules at module universe `u` commits to them and then fails on the universe
-- constraint.  It is `local`, so no global instance is declared.
attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)
  [HasDerivedCategory.{w₁} T.1.Modules]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B T.1 T.property))]
  [HasDerivedCategory.{w₃} S.1.Modules]
  [HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheaf B S.1 S.property))]

/-! ### Vanishing in negative degrees -/

omit [HasDerivedCategory.{w₁} T.1.Modules] [HasDerivedCategory.{w₃} S.1.Modules] in
/-- **The left-hand side of the Zariski comparison vanishes in negative degrees.**  The higher
direct image along `f_small` of an associated module is zero in every degree `i < 0`, the right
derived functors of an additive functor being zero below degree `0`. -/
public theorem isZero_rightDerivedPlus_pushforward_associatedModule_of_neg (i : ℤ) (hi : i < 0)
    (𝓕 : T.1.Modules) :
    IsZero (((SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i).obj
      ((associatedModule B T.1 T.property).obj 𝓕)) :=
  (SheafOfModules.pushforward.{u} (structureMapRing B f)).isZero_rightDerivedPlus_of_neg
    ((associatedModule B T.1 T.property).obj 𝓕) i hi

omit [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B T.1 T.property))]
  [HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheaf B S.1 S.property))] in
/-- **The right-hand side of the Zariski comparison vanishes in negative degrees.**  The
associated module of the `i`-th higher direct image of an `𝒪_T`-module along `f` is zero for
`i < 0`: the higher direct image is, and `𝓕 ↦ 𝓕^a` is additive. -/
public theorem isZero_associatedModule_rightDerivedPlus_pushforward_of_neg (i : ℤ) (hi : i < 0)
    (𝓕 : T.1.Modules) :
    IsZero ((associatedModule B S.1 S.property).obj
      (((Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i).obj 𝓕)) :=
  (associatedModule B S.1 S.property).map_isZero
    ((Scheme.Modules.pushforward (schemeHom B f)).isZero_rightDerivedPlus_of_neg 𝓕 i hi)

/-! ### The comparison at an integer degree -/

/-- **The Zariski comparison at an integer degree presented as a natural number.**  The
`AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIso` is indexed by a degree
`n : ℕ` cast into `ℤ`, because the base-change input
`StacksTag03LR.rightDerivedPlusBaseChangeIso` is; this is that isomorphism read at an integer
degree `i` together with a witness `i = n`, the one step the `ℕ`-indexed statement needs to become
a statement about `i` itself.  The same shape as
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
public noncomputable def higherDirectImageAssociatedModulePlusIntIsoOfEq {i : ℤ} (n : ℕ)
    (hin : i = (n : ℤ)) :
    associatedModule B T.1 T.property ⋙
        (SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i ≅
      (Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i ⋙
        associatedModule B S.1 S.property := by
  subst hin
  exact higherDirectImageAssociatedModulePlusIso B f n

/-- **The Zariski half of [Stacks, Tag 071N] at a nonnegative integer degree.**  For a morphism
`f : T ⟶ S` of schemes of a big Zariski site and an integer `0 ≤ i`,

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`,

naturally in `𝓕`, with the higher right derived functors taken as
`CategoryTheory.Functor.rightDerivedPlus` in the integer degree `i` itself.

This is `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIso` at `i.toNat`,
transported along `(i.toNat : ℤ) = i`; it is not a second proof.  The hypothesis `0 ≤ i` is
exactly what that transport needs, and nothing is lost by it: both sides vanish in negative
degrees, by
`AlgebraicGeometry.SmallZariski.isZero_rightDerivedPlus_pushforward_associatedModule_of_neg` and
`AlgebraicGeometry.SmallZariski.isZero_associatedModule_rightDerivedPlus_pushforward_of_neg`.

No hypothesis is placed on `f` or on `𝓕`. -/
public noncomputable def higherDirectImageAssociatedModulePlusIntIsoOfNonneg (i : ℤ)
    (hi : 0 ≤ i) :
    associatedModule B T.1 T.property ⋙
        (SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i ≅
      (Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i ⋙
        associatedModule B S.1 S.property :=
  higherDirectImageAssociatedModulePlusIntIsoOfEq B f i.toNat (Int.toNat_of_nonneg hi).symm

/-- **The Zariski half of [Stacks, Tag 071N] at an arbitrary integer degree.**  For every `i : ℤ`,

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`,

naturally in `𝓕`, in the `ℤ`-indexed derived-category convention of [Stacks, Tag 05U4] that the
tag is read in.

In degrees `0 ≤ i` this is
`AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntIsoOfNonneg`, which is
where the content is.  In degrees `i < 0` both sides are zero objects and this is the unique
isomorphism between them; the statement is true there but says nothing, so a consumer that wants
the comparison should prefer the nonnegative-degree form.

No hypothesis is placed on `f` or on `𝓕`.  [Stacks, Tag 071N] states the comparison for `f`
quasi-compact and quasi-separated and `𝓕` quasi-coherent; those are what the tag needs in order
that `(R ⁱ f_* 𝓕)^a` be formed on the *étale* site, where `𝓕 ↦ 𝓕^a` is only defined on the
quasi-coherent modules.  On the Zariski site it is defined on all of `Mod(𝒪_T)` and the comparison
holds with nothing assumed, so this is the tag's Zariski clause with its hypotheses dropped, not
weakened. -/
@[stacks 071N "the ZARISKI topology of the two the tag states (\"for either the étale or \
Zariski topology\"), at every integer degree and naturally in the module, with the tag's \
hypotheses on f and on the module dropped rather than weakened.  The ÉTALE topology, at the \
tag's hypotheses (f quasi-compact and quasi-separated, F quasi-coherent), in every degree and \
naturally in F, is SmallEtale.higherDirectImageAssociatedModuleIso"]
public noncomputable def higherDirectImageAssociatedModulePlusIntIso (i : ℤ) :
    associatedModule B T.1 T.property ⋙
        (SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i ≅
      (Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i ⋙
        associatedModule B S.1 S.property :=
  if hi : 0 ≤ i then higherDirectImageAssociatedModulePlusIntIsoOfNonneg B f i hi
  else
    ((Functor.isZero_iff _).2 fun 𝓕 ↦
          isZero_rightDerivedPlus_pushforward_associatedModule_of_neg B f i
            (not_le.1 hi) 𝓕).iso
      ((Functor.isZero_iff _).2 fun 𝓕 ↦
        isZero_associatedModule_rightDerivedPlus_pushforward_of_neg B f i (not_le.1 hi) 𝓕)

/-- **The Zariski half of [Stacks, Tag 071N] at one module, in an integer degree.**  For an
`𝒪_T`-module `𝓕` and a degree `i : ℤ`,

`(R ⁱ f_{small, *})(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`.

This is the component at `𝓕` of
`AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntIso`, so its naturality in
`𝓕` is `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIntObjIso_naturality`.
Its content is concentrated in the degrees `0 ≤ i`, as recorded there. -/
public noncomputable def higherDirectImageAssociatedModulePlusIntObjIso (i : ℤ)
    (𝓕 : T.1.Modules) :
    ((SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i).obj
        ((associatedModule B T.1 T.property).obj 𝓕) ≅
      (associatedModule B S.1 S.property).obj
        (((Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i).obj 𝓕) :=
  (higherDirectImageAssociatedModulePlusIntIso B f i).app 𝓕

/-- **Naturality of the Zariski comparison of [Stacks, Tag 071N] in the module, in an integer
degree.**  The comparison at a degree `i : ℤ` commutes with the associated module of every
morphism `α : 𝓕 ⟶ 𝓖` of `𝒪_T`-modules. -/
public theorem higherDirectImageAssociatedModulePlusIntObjIso_naturality (i : ℤ)
    {𝓕 𝓖 : T.1.Modules} (α : 𝓕 ⟶ 𝓖) :
    ((SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus i).map
          ((associatedModule B T.1 T.property).map α) ≫
        (higherDirectImageAssociatedModulePlusIntObjIso B f i 𝓖).hom =
      (higherDirectImageAssociatedModulePlusIntObjIso B f i 𝓕).hom ≫
        (associatedModule B S.1 S.property).map
          (((Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus i).map α) :=
  (higherDirectImageAssociatedModulePlusIntIso B f i).hom.naturality α

end AlgebraicGeometry.SmallZariski

end
