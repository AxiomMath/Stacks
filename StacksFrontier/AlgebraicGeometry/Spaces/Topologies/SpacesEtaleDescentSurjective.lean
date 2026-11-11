module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentEtaleLocal

/-!
# Descent of étale sheaves along a surjective integral, proper or flat morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. If `f` is surjective and integral, or surjective and proper, or surjective and flat
and locally of finite presentation, then sheaves on the spaces-étale site of `Y` are
equivalent, through the canonical descent datum, to descent data for the one-member family
`{f}` (Stacks 0GFW).

The source proves this by reducing to the case of a morphism which, after precomposition with
some further morphism, is representable by schemes and still has one of the three properties;
that reduction is Stacks 0GFV, and the representable case is Stacks 0GFU. This file gives the
three-case analysis of the source proof relative to two named statements: Stacks 0GFV, as
`AlgebraicGeometry.Space.DescentEffectiveAlongRepresentablePrecomposition`, and the proper
case, as `AlgebraicGeometry.Space.DescentEffectiveAlongProperSurjective`. Both are proved in
the library: Stacks 0GFV is
`AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp`
and the proper case is `AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective`. The
unconditional Stacks 0GFW, registered with its tag, is
`Space.isEquivalence_toDescentData_singleton_of_isSurjectiveIntegralProperOrFlatLfp`
in `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentProperSurjective`, which
applies the theorem of this file to those two proofs.

In the integral case the morphism is already representable, so the precomposition is the
identity, and in the flat case a scheme atlas of the source does the job, since an étale
morphism is flat and locally of finite presentation. The proper case is the one the source
proves by étale localization on the target followed by Stacks 09YC, the existence of a finite
surjective cover of a quasi-compact quasi-separated algebraic space by a scheme.

## Main definitions

* `AlgebraicGeometry.Space.IsSurjectiveDescentMorphism` is the disjunction of the three
  alternative hypotheses of Stacks 0GFW.
* `AlgebraicGeometry.Space.DescentEffectiveAlongRepresentablePrecomposition` is the statement
  of Stacks 0GFV about the big fppf site.
* `AlgebraicGeometry.Space.DescentEffectiveAlongProperSurjective` is the statement of the
  proper case of Stacks 0GFW about the big fppf site.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_isIntegralHom` and
  `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_isFlat` are the integral
  and the flat case of Stacks 0GFW, each derived from the statement of Stacks 0GFV.
* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_isSurjectiveDescentMorphism`
  derives Stacks 0GFW for the pseudofunctor of spaces-étale inverse images from the two
  statements named above.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_yonedaSpace_comp`: a morphism of
  algebraic spaces out of a representable one is relatively representable, which is how each
  of the three cases meets the representability condition of Stacks 0GFV.

## Implementation notes

The descent-data category and the comparison functor are those of
`CategoryTheory.Pseudofunctor.toDescentData` applied to
`AlgebraicGeometry.Space.spacesEtalePseudofunctor`, exactly as in the statements of
Stacks 0GFS and Stacks 0GFT; the one-member family is indexed by `Unit`.

Relative representability of a morphism out of a representable algebraic space is
`CategoryTheory.Functor.relativelyRepresentable.of_diag` applied to the representable diagonal
of the target, which is one of the three conditions of `AlgebraicGeometry.IsAlgebraicSpace`.
Its binary-product hypotheses on the big fppf site are supplied from the terminal object and
pullbacks of that site.

## References

* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 0GFV](https://stacks.math.columbia.edu/tag/0GFV)
* [Stacks Project, Tag 0GFU](https://stacks.math.columbia.edu/tag/0GFU)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The three alternative hypotheses -/

/-- The disjunction of the three alternative hypotheses of Stacks 0GFW on a morphism of
algebraic spaces over `S`: surjective and integral, surjective and proper, or surjective and
flat and locally of finite presentation. -/
abbrev IsSurjectiveDescentMorphism {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  (IsSurjective B S hS f ∧ IsIntegralHom B S hS f) ∨
    (IsSurjective B S hS f ∧ IsProper B S hS f) ∨
    (IsSurjective B S hS f ∧ IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f)

/-! ### The two statements the three-case analysis is relative to -/

/-- The statement of Stacks 0GFV about the big fppf site `B` over `S`, proved in the library as
`AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp`:
if some precomposition `π ≫ g` of a morphism `g : X ⟶ Y` of algebraic spaces is
representable by schemes and is surjective and integral, surjective and proper, or surjective
and flat and locally of finite presentation, then sheaves on the spaces-étale site of `Y` are
equivalent to descent data for `{g}`. -/
abbrev DescentEffectiveAlongRepresentablePrecomposition : Prop :=
  ∀ {X' X Y : AlgebraicSpaces B S hS} (π : X' ⟶ X) (g : X ⟶ Y),
    yoneda.relativelyRepresentable (π ≫ g).hom →
    IsSurjectiveDescentMorphism B S hS (π ≫ g).hom →
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => g)).IsEquivalence

/-- The statement of the proper case of Stacks 0GFW about the big fppf site `B` over `S`: along a
proper surjective morphism of algebraic spaces, sheaves on the spaces-étale site of the target
are equivalent to descent data. The source proves it by localizing on the target until it is
affine, where the source is quasi-compact and separated, and then taking for the precomposition
of Stacks 0GFV a finite surjective cover of the source by a scheme, which is Stacks 09YC. It is
proved in the library as `AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective`. -/
abbrev DescentEffectiveAlongProperSurjective : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y),
    IsSurjective B S hS g.hom → IsProper B S hS g.hom →
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => g)).IsEquivalence

/-! ### Representability of a morphism out of a representable algebraic space -/

/-- A morphism of algebraic spaces over `S` whose source is the algebraic space represented by
an object of the big fppf site is relatively representable: the diagonal of the target is
relatively representable because the target is an algebraic space. -/
theorem relativelyRepresentable_of_yonedaSpace_comp {U : BigFppfOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (g : yoneda.obj U ⟶ Y) : yoneda.relativelyRepresentable g := by
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact hY.diagonal_representable.of_diag g

/-! ### The three cases -/

/-- The integral case of Stacks 0GFW, derived from the statement of Stacks 0GFV. An integral
morphism of algebraic spaces is representable by schemes, so Stacks 0GFV applies with the
identity as the precomposition. -/
theorem isEquivalence_toDescentData_singleton_of_isIntegralHom
    (hGFV : DescentEffectiveAlongRepresentablePrecomposition B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hint : IsIntegralHom B S hS f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  have hrep : yoneda.relativelyRepresentable f.hom :=
    ((isIntegralHom_iff_representable B S hS f.hom X.property Y.property).mp hint).1
  exact hGFV (𝟙 X) f (by rw [Category.id_comp]; exact hrep)
    (by rw [Category.id_comp]; exact Or.inl ⟨hsurj, hint⟩)

/-- The flat case of Stacks 0GFW, derived from the statement of Stacks 0GFV. A scheme atlas of
the source is surjective, flat and locally of finite presentation because it is surjective and
étale, so its composite with `f` is again surjective, flat and locally of finite presentation,
and it is representable because its source is representable. Stacks 0GFV then applies. -/
theorem isEquivalence_toDescentData_singleton_of_isFlat
    (hGFV : DescentEffectiveAlongRepresentablePrecomposition B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  obtain ⟨U, a, hasurj, haetale⟩ := X.property.exists_atlas
  let X' : AlgebraicSpaces B S hS := (schemeSpaceFunctor B S hS).obj U
  let π : X' ⟶ X := ObjectProperty.homMk a
  have haet : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale
  have hasurj' : IsSurjective B S hS a :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.property U a).mp hasurj
  have haflat : IsFlat B S hS a := isFlat_of_isEtale B S hS haet
  have hafp : IsLocallyOfFinitePresentation B S hS a :=
    isLocallyOfFinitePresentation_of_isEtale B S hS haet
  have hcomp : IsSurjectiveDescentMorphism B S hS (π ≫ f).hom :=
    Or.inr (Or.inr
      ⟨isSurjective_comp B S hS hasurj' hsurj,
        isFlat_comp B S hS X'.property X.property Y.property a f.hom haflat hflat,
        isLocallyOfFinitePresentation_comp B S hS X'.property X.property Y.property a f.hom
          hafp hfp⟩)
  exact hGFV π f (relativelyRepresentable_of_yonedaSpace_comp B S hS Y.property _) hcomp

/-! ### Stacks 0GFW -/

/-- Stacks 0GFW for the pseudofunctor of spaces-étale inverse images, derived from the statements
of Stacks 0GFV and of the proper case. Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` which is surjective and integral, or surjective and
proper, or surjective and flat and locally of finite presentation. Then sheaves on the
spaces-étale site of `Y` are equivalent, through the canonical descent datum, to descent data
for the one-member family `{f}`.

The integral and the flat case are derived from `hGFV`, the statement of Stacks 0GFV; the proper
case is `hproper`. Both are proved in the library, and
`Space.isEquivalence_toDescentData_singleton_of_isSurjectiveIntegralProperOrFlatLfp`,
which carries the tag 0GFW, is this theorem applied to those proofs. -/
theorem isEquivalence_toDescentData_singleton_of_isSurjectiveDescentMorphism
    (hGFV : DescentEffectiveAlongRepresentablePrecomposition B S hS)
    (hproper : DescentEffectiveAlongProperSurjective B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsSurjectiveDescentMorphism B S hS f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  obtain ⟨hsurj, hint⟩ | ⟨hsurj, hpr⟩ | ⟨hsurj, hflat, hfp⟩ := hf
  · exact isEquivalence_toDescentData_singleton_of_isIntegralHom B S hS hGFV f hsurj hint
  · exact hproper f hsurj hpr
  · exact isEquivalence_toDescentData_singleton_of_isFlat B S hS hGFV f hsurj hflat hfp

end AlgebraicGeometry.Space

end
