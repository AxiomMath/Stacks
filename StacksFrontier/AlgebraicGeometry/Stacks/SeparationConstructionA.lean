module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The separation conditions of a 1-morphism are unchanged by Construction A

Let `g : S ⟶ S'` be a morphism of a big fppf site. Construction A of Stacks, Section 04WT views
an algebraic stack over `S` as an algebraic stack over `S'`, and Stacks 04X5 says that it is
bijective on 1-morphisms; the bijection is
`AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv`. This file proves that the
Deligne–Mumford and quasi-DM conditions of Stacks 04YW on a 1-morphism are preserved and
reflected by that bijection.

The conditions of Stacks 04YW are conditions on the *relative* diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`, and the content is that the relative diagonal is unchanged by
Construction A. That is a statement about the self-product, and it is where the relative case
parts company with the absolute one: for the *absolute* diagonal the self-product **grows**, the
self-product of `changeBase 𝒳` over the big fppf site of `S'` having the strictly larger object
set of pairs lying over a common `S'`-scheme by two different morphisms to `S`
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`
has to route around it through the conditions of Stacks 045G, and
`CategoryTheory.TwoFibreProductOver.absoluteFibreFunctor` is only fully faithful). For the
relative diagonal it does **not** grow: the comparison isomorphism of an object of the
self-product lies in `𝒴`, and `CategoryTheory.TwoFibreProductOver.obj_eq_of_vertical` reads off
that its structure image is a morphism of the site of `S` whose underlying morphism is an
identity, which forces the two components to lie over the *same* object of the site of `S`. So
`CategoryTheory.TwoFibreProductOver.relocalizeBase` is an isomorphism of categories here, and the
whole transfer is that isomorphism together with the two compatibilities proved below: it is
strictly over the base, and it carries the diagonal to the diagonal.

With those in hand the transfer is the composite of two known statements. Stacks 0457 in the
form `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` moves the relative property
across the comparison at the *fixed* base `S'`; and
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff` — stated at an arbitrary
property of morphisms of schemes precisely because, as its own docstring says, that is what the
separation axioms of Stacks 04YW need of it — moves it between the two bases. Representability by
algebraic spaces travels the same two steps, by Stacks 0457 in the form
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` and by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.diagonal_comp_relocalizeBase`: relocalizing the base
  carries the diagonal to the diagonal, strictly.
* `AlgebraicGeometry.Stack.changeBaseSelfProductHom` and `...changeBaseSelfProductInv`: the
  comparison between Construction A of the self-product of `f` and the self-product of
  Construction A of `f`, in each direction, as 1-morphisms over the big fppf site of `S'`.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_relativeDiagonal_changeBaseHom_iff`: the relative
  property of Stacks 03YK of the relative diagonal is unchanged by the comparison, for an
  **arbitrary** property of morphisms of algebraic spaces over `S'`. This is the
  property-agnostic half, and it is what the separated and quasi-separated conditions of
  Stacks 04YW need as well.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBaseHom_iff`.
* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_relativeDiagonal_changeBaseHom_iff`: the
  every-étale-chart relative property of the relative diagonal is the same over `S` and over
  `S'`, at an arbitrary property of morphisms of schemes.
* `AlgebraicGeometry.Stack.isDM_changeBase_iff` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_changeBase_iff`: **the two conditions of
  Stacks 04YW that are every-étale-chart conditions are unchanged by Construction A.**

## Implementation notes

**No declaration here carries a Stacks attribute.** The transfer is not a Stacks tag of its own:
Stacks 04YW is the *definition* of the four conditions, and all four of its keys are already
registered in this library, while the statements that consume this transfer are parts (5)–(8) of
Stacks 050L, whose covering set is its eight assertions and none of which is proved here. Whoever
lands those parts must reuse these declarations rather than re-coin them.

The separated and quasi-separated conditions are **not** transferred here. Their properties are
`AlgebraicGeometry.Space.IsProper` and quasi-compactness-with-quasi-separatedness, whose passage
between the two bases is available only in one direction
(`AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of`,
`...isQuasiCompact_spacesOverSmallerBaseFunctor_of`,
`...isQuasiSeparated_spacesOverSmallerBaseFunctor_of`), so they give an implication and not an
equivalence; `relativeProperty_relativeDiagonal_changeBaseHom_iff` is stated at an arbitrary
property so that half of the work is already done for them.

The two comparison 1-morphisms are not interchangeable as *based* functors even though they are
mutually inverse functors. `CategoryTheory.TwoFibreProductOver.relocalizeBase` is strictly over
the base, so its commutation is `rfl`; the backward comparison reads the base off its
`𝒳`-component instead, and its commutation has to be routed through the two instances of
`CategoryTheory.TwoFibreProductOver.fst_comp_eq`. Both are needed, one for each direction of each
equivalence.

`StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance` is imported for
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`, the invariance of
representability under equivalences, and is named here rather than reached transitively.

`CategoryTheory.BasedFunctor.id` has no `Functor.IsEquivalence` instance for its underlying
functor — the identity based functor is a plain `def`, so instance search does not see the
identity functor through it — and the three proofs below supply it by `change` rather than
registering a global instance for it.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {T : Type u₁} [Category.{v₁} T] {Y Y' : T} (g : Y ⟶ Y')
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ Over Y} {p𝒴 : 𝒴 ⥤ Over Y} {p𝒮 : 𝒮 ⥤ Over Y} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **Relocalizing the base carries the diagonal to the diagonal, strictly.** The diagonal sends
an object to the triple `(x, x, 𝟙)`, and relocalizing the base changes only the base object,
which is the image of the old one; the comparison isomorphism and both components are untouched,
so the two functors are literally the same. -/
lemma diagonal_comp_relocalizeBase {G : 𝒳 ⥤ 𝒮} (hG : G ⋙ p𝒮 = p𝒳)
    (hG' : G ⋙ (p𝒮 ⋙ Over.map g) = p𝒳 ⋙ Over.map g) :
    diagonal hG ⋙ relocalizeBase g = diagonal hG' :=
  rfl

/-- **The forward comparison is strictly over the base.** -/
lemma relocalizeBase_comp_structureFunctor :
    relocalizeBase (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F) (G := G) g ⋙
        structureFunctor (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G =
      structureFunctor p𝒳 p𝒴 p𝒮 F G ⋙ Over.map g :=
  rfl

/-- **The backward comparison is over the base.** It reads the base of an object off the object's
`𝒳`-component, so the commutation is not an identity but the two instances of
`CategoryTheory.TwoFibreProductOver.fst_comp_eq` either side of the strict identity
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase_comp_fst`. -/
lemma unrelocalizeBase_comp_structureFunctor (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    unrelocalizeBase (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F) (G := G) g hF hG ⋙
        (structureFunctor p𝒳 p𝒴 p𝒮 F G ⋙ Over.map g) =
      structureFunctor (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G := by
  rw [← fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F) (G := G),
    ← Functor.assoc, ← Functor.assoc, unrelocalizeBase_comp_fst, Functor.assoc, fst_comp_eq]

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-! ### The comparison of the two self-products -/

/-- **Construction A of the self-product of `f` is the self-product of Construction A of `f`**,
forward direction: `CategoryTheory.TwoFibreProductOver.relocalizeBase`, which is strictly over
the big fppf site of `S'`. -/
def changeBaseSelfProductHom (f : 𝒳 ⟶ 𝒴) :
    (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val ⥤ᵇ
      (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseHom B S S' hS hS' g f).hom
        (changeBaseHom B S S' hS hS' g f).hom).val where
  toFunctor := TwoFibreProductOver.relocalizeBase g
  w := TwoFibreProductOver.relocalizeBase_comp_structureFunctor g

/-- The backward comparison, `CategoryTheory.TwoFibreProductOver.unrelocalizeBase`. Its
commutation with the two structure functors is
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase_comp_structureFunctor`, and the two
hypotheses it needs are both the commutation of `f` with the structure functors. -/
def changeBaseSelfProductInv (f : 𝒳 ⟶ 𝒴) :
    (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseHom B S S' hS hS' g f).hom
        (changeBaseHom B S S' hS hS' g f).hom).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val where
  toFunctor := TwoFibreProductOver.unrelocalizeBase g f.hom.w f.hom.w
  w := TwoFibreProductOver.unrelocalizeBase_comp_structureFunctor g f.hom.w f.hom.w

/-- The forward comparison `changeBaseSelfProductHom` is an equivalence of categories. -/
instance isEquivalence_changeBaseSelfProductHom (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (changeBaseSelfProductHom B S S' hS hS' g f).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g f.hom.w f.hom.w).isEquivalence_functor

/-- The backward comparison `changeBaseSelfProductInv` is an equivalence of categories. -/
instance isEquivalence_changeBaseSelfProductInv (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (changeBaseSelfProductInv B S S' hS hS' g f).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g f.hom.w f.hom.w).isEquivalence_inverse

/-- **Construction A carries the relative diagonal to the relative diagonal**, strictly. -/
lemma changeBaseHom_relativeDiagonal_comp (f : 𝒳 ⟶ 𝒴) :
    BasedFunctor.comp (changeBaseHom B S S' hS hS' g
          (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
        (changeBaseSelfProductHom B S S' hS hS' g f) =
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom :=
  BasedCategory.BasedFunctor.ext'
    (TwoFibreProductOver.diagonal_comp_relocalizeBase g f.hom.w
      (changeBaseHom B S S' hS hS' g f).hom.w)

/-- The same identity read through the backward comparison. -/
lemma relativeDiagonal_changeBaseHom_comp (f : 𝒳 ⟶ 𝒴) :
    BasedFunctor.comp (relativeDiagonal.{u, u, u + 1} B S' hS'
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
          (changeBaseHom B S S' hS hS' g f)).hom
        (changeBaseSelfProductInv B S S' hS hS' g f) =
      (changeBaseHom B S S' hS hS' g
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom := by
  refine BasedCategory.BasedFunctor.ext' ?_
  show TwoFibreProductOver.diagonal f.hom.w ⋙ TwoFibreProductOver.relocalizeBase g ⋙
      TwoFibreProductOver.unrelocalizeBase g f.hom.w f.hom.w =
    TwoFibreProductOver.diagonal f.hom.w
  rw [TwoFibreProductOver.relocalizeBase_comp_unrelocalizeBase, Functor.comp_id]

/-- The identity based functor of the base change of `𝒳` has an equivalence as underlying
functor. -/
private theorem isEquivalence_basedFunctor_id_changeBase (𝒳 : CatFiberedInGroupoids.{u, u, u + 1}
    (BigFppfOver B S hS)) :
    Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor := by
  change Functor.IsEquivalence (𝟭 _)
  infer_instance

/-! ### The transfer of the relative diagonal's relative property -/

/-- **The relative property of the relative diagonal is unchanged by Construction A, at the
fixed base `S'`.** The property is arbitrary, and the quantifier is written out rather than taken
through `AlgebraicGeometry.Stack.HasRelativeProperty`, which carries two instance arguments the
argument does not use and which are unavailable for the properties of Stacks 04YW. -/
theorem relativeProperty_relativeDiagonal_changeBaseHom_iff
    (P : MorphismProperty (AlgebraicSpaces B S' hS')) (f : 𝒳 ⟶ 𝒴) :
    (∀ (U : BigFppfOver B S' hS')
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseHom B S S' hS hS' g f).hom
            (changeBaseHom B S S' hS hS' g f).hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseHom B S S' hS hS' g f).hom
            (changeBaseHom B S S' hS hS' g f).hom).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
            (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseHom B S S' hS hS' g f).hom
              (changeBaseHom B S S' hS hS' g f).hom).val.p y
            (CatFiberedInGroupoids.homFunctor (relativeDiagonal.{u, u, u + 1} B S' hS'
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
              (changeBaseHom B S S' hS hS' g f))))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S' hS' U
          ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj ⟨F, hF⟩))) ↔
      (∀ (U : BigFppfOver B S' hS')
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (changeBaseFiberedInGroupoids B S S' hS hS' g
            (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val.obj)
        (_hy : y ⋙ (changeBaseFiberedInGroupoids B S S' hS hS' g
            (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
            (changeBaseFiberedInGroupoids B S S' hS hS' g
              (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val.p y
            (CatFiberedInGroupoids.homFunctor (changeBaseHom B S S' hS hS' g
              (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f))))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S' hS' U
          ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj ⟨F, hF⟩))) := by
  have hid := isEquivalence_basedFunctor_id_changeBase B S S' hS hS' g 𝒳
  exact ⟨relativeProperty_of_equivalences B S' hS' P
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val)
      (changeBaseSelfProductHom B S S' hS hS' g f)
      (eqToIso (changeBaseHom_relativeDiagonal_comp B S S' hS hS' g f).symm),
    relativeProperty_of_equivalences B S' hS' P
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val)
      (changeBaseSelfProductInv B S S' hS hS' g f)
      (eqToIso (relativeDiagonal_changeBaseHom_comp B S S' hS hS' g f).symm)⟩

/-- **Representability by algebraic spaces of the relative diagonal is unchanged by
Construction A.** Stacks 0457 across the comparison, then Stacks 04X5 between the two bases. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBaseHom_iff (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S' hS'
        (relativeDiagonal.{u, u, u + 1} B S' hS'
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
          (changeBaseHom B S S' hS hS' g f)).hom ↔
      IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f).hom := by
  have hid := isEquivalence_basedFunctor_id_changeBase B S S' hS hS' g 𝒳
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S' hS'
    (relativeDiagonal.{u, u, u + 1} B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
      (changeBaseHom B S S' hS hS' g f)).hom
    (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
    (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val)
    (changeBaseSelfProductInv B S S' hS hS' g f)
    (eqToIso (relativeDiagonal_changeBaseHom_comp B S S' hS hS' g f).symm)).symm.trans
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f).hom)

/-- **The every-étale-chart relative property of the relative diagonal is the same over `S` and
over `S'`.** The comparison at the fixed base `S'`, composed with the arbitrary-property form of
Stacks 04X5 between the two bases. -/
theorem holdsOnEveryEtaleChart_relativeDiagonal_changeBaseHom_iff
    (Q : MorphismProperty Scheme.{u}) (f : 𝒳 ⟶ 𝒴)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f).hom) :
    (∀ (U : BigFppfOver B S' hS')
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseHom B S S' hS hS' g f).hom
            (changeBaseHom B S S' hS hS' g f).hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
            (changeBaseHom B S S' hS hS' g f).hom
            (changeBaseHom B S S' hS hS' g f).hom).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
            (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseHom B S S' hS hS' g f).hom
              (changeBaseHom B S S' hS hS' g f).hom).val.p y
            (CatFiberedInGroupoids.homFunctor (relativeDiagonal.{u, u, u + 1} B S' hS'
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
              (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
              (changeBaseHom B S S' hS hS' g f))))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.HoldsOnEveryEtaleChart B S' hS' Q
          (algebraicSpaceMap B S' hS' U
            ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj
              ⟨F, hF⟩)).hom) ↔
      (∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p
            (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.p y
            (CatFiberedInGroupoids.homFunctor (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.HoldsOnEveryEtaleChart B S hS Q
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :=
  (relativeProperty_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g
      (fun _ _ m => Space.HoldsOnEveryEtaleChart B S' hS' Q m.hom) f).trans
    (hasRelativeProperty_smooth_changeBaseHom_iff.{u, u, u + 1} B S S' hS hS' g Q
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f) hΔ)

/-- An existential over a proposition is invariant under an equivalence of the witness
propositions, when the dependent bodies agree given a witness on the right. -/
private theorem exists_iff_of_iff_of_imp {A A' C C' : Prop} (h : A' ↔ A) (hC : A → (C' ↔ C)) :
    (∃ _ : A', C') ↔ ∃ _ : A, C :=
  ⟨fun ⟨a, c⟩ => ⟨h.1 a, (hC (h.1 a)).1 c⟩, fun ⟨a, c⟩ => ⟨h.2 a, (hC a).2 c⟩⟩

/-! ### The two every-étale-chart conditions of Stacks 04YW -/

/-- **The Deligne–Mumford condition of Stacks 04YW is unchanged by Construction A.** A
1-morphism of algebraic stacks over `S` is DM exactly when the 1-morphism over `S'` that the
hom-bijection of Stacks 04X5 assigns to it is DM. Unramifiedness of a morphism of algebraic
spaces is the every-étale-chart condition at `AlgebraicGeometry.Unramified`. -/
theorem isDM_changeBase_iff {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsDM B S' hS' (𝒳 := changeBaseAlgebraicStack B S S' hS hS' g 𝒳)
        (𝒴 := changeBaseAlgebraicStack B S S' hS hS' g 𝒴)
        (Bicategory.InducedBicategory.mkHom
          (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 f).val) ↔
      IsDM B S hS f := by
  exact exists_iff_of_iff_of_imp
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g f.hom)
    (holdsOnEveryEtaleChart_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g
      (@AlgebraicGeometry.Unramified.{u}) f.hom)

/-- **The quasi-DM condition of Stacks 04YW is unchanged by Construction A.** Local
quasi-finiteness of a morphism of algebraic spaces is the every-étale-chart condition at
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`. -/
theorem AlgebraicStacks.isQuasiDM_changeBase_iff
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal B S' hS'
        (𝒳 := changeBaseAlgebraicStack B S S' hS hS' g 𝒳)
        (𝒴 := changeBaseAlgebraicStack B S S' hS hS' g 𝒴)
        (Bicategory.InducedBicategory.mkHom
          (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 f).val) ↔
      AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal B S hS f := by
  exact exists_iff_of_iff_of_imp
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g f.hom)
    (holdsOnEveryEtaleChart_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) f.hom)

end AlgebraicGeometry.Stack

end
