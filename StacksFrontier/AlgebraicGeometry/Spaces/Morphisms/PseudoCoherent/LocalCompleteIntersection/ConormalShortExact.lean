module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Short exactness of the conormal sequence of a local complete intersection morphism of spaces

Let `Z ⟶ Y ⟶ X` be formally unramified morphisms of algebraic spaces over a scheme `S` and
assume `Z ⟶ Y` is a local complete intersection morphism.  Stacks 06CC asserts that the conormal
sequence

```
  0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0
```

of Stacks 06BD is short exact, `i : Z ⟶ Y` being the first of the two morphisms.  This file
proves the étale localization step and the reduction of short exactness to injectivity of the
left-hand arrow; Stacks 06CC itself is
`AlgebraicGeometry.Space.conormalSequence_shortExact_of_isLocalCompleteIntersection` in
`ConormalShortExactUnconditional.lean`, in the same directory as this file.

## The sequence, and where it lives

As in `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` (Stacks 06BF),
formal unramifiedness of the two morphisms is presented by universal first-order thickenings
`Z ⊂ Z'` over `X` and `Y ⊂ Y'` over `X`, which is what it amounts to by Stacks 0606; `𝒞_{Z/X}`
is then the conormal module of `Z` in `Z'`, and `𝒞_{Z/Y}` the conormal module of the copy of `Z`
inside `Y ×_{Y'} Z'`.  That copy is the inverse image of `Z ⊆ Z'` along the inclusion of the
fibre product, and the sequence is read on it, along the projection `π` of that inverse image:
the right-hand arrow is the map of conormal modules of Stacks 04CP whose surjectivity is
clause (2) of Stacks 06BF, and the left-hand arrow is `π^*` of the conormal map of
Stacks 060A at the square of `AlgebraicGeometry.Space.universalThickeningComp_square`.

## Main results

* `AlgebraicGeometry.Space.mono_modulePullback_schemeChart_iff`: injectivity of a map of modules
  on the small étale site of an algebraic space is étale local — it holds exactly when it holds
  after inverse image along an étale scheme chart surjective on points.  This is the étale
  localization step of the proof of Stacks 06CC.
* `AlgebraicGeometry.Space.mono_universalThickeningCompConormalLeftMap_of_chart`: that step for
  the left-hand arrow of the sequence — injectivity after inverse image along one étale chart
  surjective on points gives injectivity on the algebraic space.
* `AlgebraicGeometry.Space.shortExact_iff_mono_universalThickeningCompConormalLeftMap`: granted
  the vanishing of the composite and exactness at `𝒞_{Z/X}`, short exactness of the sequence is
  exactly injectivity of its left-hand arrow; the epimorphism at the right term is discharged
  from clause (2) of Stacks 06BF.

## What is carried

* `hzero` and `hmid`, the vanishing of the composite and exactness at `𝒞_{Z/X}`.  These are the
  two clauses of Stacks 06BD that Stacks 06CC takes for granted when it speaks of "the exact
  sequence of Lemma 06BD", so they are not clauses of this tag, and neither is available here:
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean` carries only
  `@[stacks 06BD "exactness at the right term"]`,
  `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` only
  `@[stacks 06BF "clause (2): exactness at the right term …"]`, and
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderNeighbourhood.lean` records that
  the middle exactness of Stacks 06BD "is absent at the level of algebraic spaces and of schemes
  alike".
* `AlgebraicGeometry.Space.UniversalThickeningCompConormalMonoTransfer`, injectivity of the
  left-hand arrow.  This is the clause of Stacks 06CC, and it is carried because the case of
  schemes it reduces to is not importable.  Stacks 06BA *is* proved for schemes, by
  `Stacks.Thickenings.mono_transitivityConormalLeftMap` in
  `StacksFrontier/AlgebraicGeometry/Thickenings/TransitivityConormalShortExact.lean`, but that
  declaration and the short exactness beside it are written `theorem` rather than
  `public theorem`, so they are local to their module and no other module can use them; nothing
  outside that file refers to either.  The carry takes the local complete intersection hypothesis
  as its antecedent, so nothing is granted about a morphism which is not Koszul, and by
  `mono_universalThickeningCompConormalLeftMap_of_chart` it is implied by the same statement
  after inverse image along one étale scheme chart surjective on points, which is the shape in
  which the reduction to schemes delivers it: exporting the scheme-level result would discharge
  this carry through that bridge, with no change to any statement here.

## References

* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA), the case of schemes.
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD) and
  [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF), the sequence.
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A), the left-hand arrow.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the right-hand arrow.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), exactness of the
  inverse image of modules along an étale morphism.
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Injectivity of a map of modules is étale local -/

/-- **Injectivity of a map of modules on the small étale site is étale local.**  For an étale
scheme chart `a` of an algebraic space which is surjective on points, a map of modules is a
monomorphism exactly when its inverse image along `a` is: the inverse image is exact by
Stacks 03LV, hence preserves monomorphisms, and it is faithful because `a` is surjective, hence
reflects them. -/
public theorem mono_modulePullback_schemeChart_iff {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X.1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Mono ((modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).map φ) ↔ Mono φ := by
  have hEt : IsEtale B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
    isEtale_of_presheaf_etale B S hS haEtale
  have hfaithful : (modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).Faithful :=
    faithful_modulePullback B S hS U (ObjectProperty.homMk a) hEt haSurj
  have hlim : PreservesFiniteLimits (modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)) :=
    ((exactFunctor_iff _).mp (modulePullback_exact B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X) hEt)).1
  refine ⟨fun h => (modulePullback B S hS
    (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mono_of_mono_map h, fun h => ?_⟩
  have := h
  infer_instance

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-! ### The two arrows of the sequence -/

/-- The copy of `Z` inside the fibre product `Y ×_{Y'} Z'`, read as an algebraic space: the
space on which the conormal sequence of the composition is a sequence of modules. -/
public noncomputable def universalThickeningCompConormalBase : AlgebraicSpaces B S hS :=
  ⟨(preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩).1.toFunctor,
    (preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩).2.1⟩

/-- The right-hand arrow `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the sequence: the map of conormal modules of
Stacks 04CP for the inclusion of the fibre product `Y ×_{Y'} Z'` into `Z'`, which is the arrow
whose surjectivity is clause (2) of Stacks 06BF. -/
public noncomputable def universalThickeningCompConormalRightMap :=
  conormalMap B S hS
    (preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
    (preimageProjection B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    (conormalEtaleRestrictionSquare B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)

/-- The left-hand arrow `i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the sequence: the inverse image, along the
projection of the copy of `Z` inside the fibre product, of the conormal map of Stacks 060A at
the square of `AlgebraicGeometry.Space.universalThickeningComp_square`. -/
public noncomputable def universalThickeningCompConormalLeftMap :=
  (modulePullback B S hS
    (preimageProjection B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)).map
    (universalThickeningConormalMap B S hS (𝟙 X : X ⟶ X) i hZ hY
      (universalThickeningComp_square B S hS i hfac))

/-! ### Injectivity of the left-hand arrow, the case of schemes -/

/-- Injectivity of the left-hand arrow of the conormal sequence of the composition, granted that
the first morphism is a local complete intersection morphism.  This is the content of
Stacks 06BA, the case of schemes; the section *What is carried* of this file says why it is
carried and what implies it. -/
public abbrev UniversalThickeningCompConormalMonoTransfer : Prop :=
  IsLocalCompleteIntersection B S hS i →
    Mono (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac)

/-- **The injectivity clause descends from an étale chart.**  Injectivity of the left-hand arrow
of the conormal sequence of the composition after inverse image along one étale scheme chart
surjective on points gives it on the algebraic space, by
`mono_modulePullback_schemeChart_iff`. -/
public theorem mono_universalThickeningCompConormalLeftMap_of_chart
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hm : Mono ((modulePullback B S hS (ObjectProperty.homMk a :
        schemeSpace U ⟶ universalThickeningCompConormalBase B S hS i hZ hY hfac)).map
      (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac))) :
    Mono (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac) :=
  (mono_modulePullback_schemeChart_iff B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac) U a haEtale haSurj).mp hm

/-- **Injectivity of the left-hand arrow for a local complete intersection morphism**, granted
the case of schemes. -/
public theorem mono_universalThickeningCompConormalLeftMap
    (hlci : IsLocalCompleteIntersection B S hS i)
    (hmono : UniversalThickeningCompConormalMonoTransfer B S hS i hZ hY hfac) :
    Mono (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac) :=
  hmono hlci

/-! ### Short exactness -/

/-- Granted the vanishing of the composite and exactness at `𝒞_{Z/X}`, the conormal sequence of
the composition is short exact exactly when its left-hand arrow is injective: the epimorphism at
the right term is clause (2) of Stacks 06BF,
`AlgebraicGeometry.Space.epi_conormalMap_comp`. -/
public theorem shortExact_iff_mono_universalThickeningCompConormalLeftMap
    (hzero : universalThickeningCompConormalLeftMap B S hS i hZ hY hfac ≫
      universalThickeningCompConormalRightMap B S hS i hZ hY hfac = 0)
    (hmid : (ShortComplex.mk _ _ hzero).Exact) :
    (ShortComplex.mk _ _ hzero).ShortExact ↔
      Mono (universalThickeningCompConormalLeftMap B S hS i hZ hY hfac) := by
  have hepi : Epi (universalThickeningCompConormalRightMap B S hS i hZ hY hfac) :=
    epi_conormalMap_comp B S hS i hZ hY hfac
  exact ⟨fun h => h.mono_f, fun h => ShortComplex.ShortExact.mk' hmid h hepi⟩

end AlgebraicGeometry.Space

end
