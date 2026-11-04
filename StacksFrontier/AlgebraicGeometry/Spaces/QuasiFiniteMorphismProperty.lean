module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Local quasi-finiteness as a morphism property of algebraic spaces (Stacks 03XK, Stacks 03XL)

Let `S` be a scheme contained in a big fppf site `B`. Being locally quasi-finite
(**Stacks 03XJ**, part (1)) is packaged here as a `CategoryTheory.MorphismProperty` on the
category `AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2, beside the six properties of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties`, and both of its permanence
properties are supplied: stability under composition (**Stacks 03XK**) and stability under base
change (**Stacks 03XL**).

The packaging is what `AlgebraicGeometry.Stack.HasRelativeProperty` takes as its argument, and
of the three instances that **Stacks 045B** asks of such a property two are proved here; the
third, locality at the target for the fppf precoverage, is **Stacks 0427** and is absent.

## Main definitions

* `AlgebraicGeometry.Space.locallyQuasiFiniteProperty`.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_comp` and
  `AlgebraicGeometry.Space.isQuasiFinite_comp`: **Stacks 03XK**, both cases.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_isStableUnderBaseChange` and
  `AlgebraicGeometry.Space.isQuasiFinite_isStableUnderBaseChange`: **Stacks 03XL**, both cases.

## Implementation notes

Both permanence properties are instances of the every-étale-chart machinery of Stacks 03MJ:
composition is **Stacks 0AML** and base change is **Stacks 0AMM**, and each asks that local
quasi-finiteness of morphisms of schemes — the conjunction of
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite` — be étale
local on the source and target, which is the locally quasi-finite item of **Stacks 04R3**, and
stable under composition, respectively base change, which each conjunct is.

The quasi-finite cases of Stacks 03XK and Stacks 03XL are their locally quasi-finite cases
paired with quasi-compactness, for which composition is **Stacks 03HG** and base change is
**Stacks 03HF**; both are available, so the two cases of each tag are proved together here.

The property is an abbreviation and is untagged, as the six of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties` are: it coins no notion, it
repackages the Chapter 67 predicate as a `CategoryTheory.MorphismProperty` on the
Stacks 02X2 category.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XK](https://stacks.math.columbia.edu/tag/03XK)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03XK**, the locally quasi-finite case: the composite of two locally quasi-finite
morphisms of algebraic spaces over `S` is locally quasi-finite.

Local quasi-finiteness of morphisms of schemes is étale local on the source and target
(**Stacks 04R3**) and stable under composition, each conjunct being, so this is an instance of
**Stacks 0AML**. -/
@[stacks 03XK "locally quasi-finite"]
theorem isLocallyQuasiFinite_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsLocallyQuasiFinite B S hS f) (hg : IsLocallyQuasiFinite B S hS g) :
    IsLocallyQuasiFinite B S hS (f ≫ g) :=
  have _ : MorphismProperty.IsStableUnderComposition
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        @AlgebraicGeometry.LocallyQuasiFinite.{u}) :=
    MorphismProperty.IsStableUnderComposition.inf
  holdsOnEveryEtaleChart_comp B S hS _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hF hG hH f g hf hg

/-- **Stacks 03XK**, the quasi-finite case: the composite of two quasi-finite morphisms of
algebraic spaces over `S` is quasi-finite.

Quasi-finiteness is local quasi-finiteness together with quasi-compactness, and the latter is
stable under composition by **Stacks 03HG**. -/
@[stacks 03XK "quasi-finite"]
theorem isQuasiFinite_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsQuasiFinite B S hS f) (hg : IsQuasiFinite B S hS g) :
    IsQuasiFinite B S hS (f ≫ g) :=
  ⟨isLocallyQuasiFinite_comp B S hS hF hG hH f g hf.1 hg.1,
    isQuasiCompact_comp B S hS hG hH f g hf.2 hg.2⟩

/-- **Stacks 03XL**, the locally quasi-finite case: being locally quasi-finite is stable under
base change.

Local quasi-finiteness of morphisms of schemes is étale local on the source and target
(**Stacks 04R3**) and stable under base change, each conjunct being, so this is an instance of
**Stacks 0AMM**. -/
@[stacks 03XL "locally quasi-finite"]
instance isLocallyQuasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyQuasiFinite B S hS f.hom) :=
  have _ : MorphismProperty.IsStableUnderBaseChange
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        @AlgebraicGeometry.LocallyQuasiFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget

/-- **Stacks 03XL**, the quasi-finite case: being quasi-finite is stable under base change.

Quasi-finiteness is local quasi-finiteness together with quasi-compactness, and the latter is
stable under base change by **Stacks 03HF**. -/
@[stacks 03XL "quasi-finite"]
instance isQuasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiFinite B S hS f.hom) where
  of_isPullback sq hg :=
    ⟨(isLocallyQuasiFinite_isStableUnderBaseChange B S hS).of_isPullback sq hg.1,
      (isQuasiCompact_isStableUnderBaseChange B S hS).of_isPullback sq hg.2⟩

/-! ### The packaged property -/

/-- Being locally quasi-finite (**Stacks 03XJ**, part (1)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev locallyQuasiFiniteProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsLocallyQuasiFinite B S hS f.hom

/-- Local quasi-finiteness of a morphism of algebraic spaces over `S` is stable under base
change, registered at `AlgebraicGeometry.Space.locallyQuasiFiniteProperty`. This is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_isStableUnderBaseChange`, which is already stated
at the packaged property. -/
instance locallyQuasiFiniteProperty_isStableUnderBaseChange :
    (locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
  isLocallyQuasiFinite_isStableUnderBaseChange B S hS

/-- Local quasi-finiteness respects isomorphisms, registered at
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty`: it is stable under base change. -/
instance locallyQuasiFiniteProperty_respectsIso :
    (locallyQuasiFiniteProperty B S hS).RespectsIso :=
  (isLocallyQuasiFinite_isStableUnderBaseChange B S hS).respectsIso

/-- Local quasi-finiteness of a morphism of algebraic spaces over `S` is stable under
composition, registered at `AlgebraicGeometry.Space.locallyQuasiFiniteProperty`. This is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_comp` with the algebraicity of the three objects
supplied by the objects themselves.

With it, and with locality at the target for the fppf precoverage
(`AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf`, **Stacks 0427**), that
property has all three instance arguments of **Stacks 045B**. -/
instance locallyQuasiFiniteProperty_isStableUnderComposition :
    (locallyQuasiFiniteProperty B S hS).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg :=
    isLocallyQuasiFinite_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

end AlgebraicGeometry.Space

end
