module

public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitePresentationFpqcLocality
import StacksCore.Tactic.StacksAttribute

/-!
# Families of algebraic spaces over an algebraic space (Stacks 0E93)

Let `T` be an algebraic space over the base scheme `S` of a big fppf site, and let `𝒮_T` be the
algebraic stack attached to it (`AlgebraicGeometry.Stack.fibredCategory`). Stacks 0E93 says that
sending a finite type morphism of algebraic spaces `X ⟶ T` to the functor over the site
`𝒮_T ⟶ Spaces'_ft`, `(U, t) ↦ U ×_T X`, is an equivalence of categories onto
`Mor_{Cat/Sch_fppf}(𝒮_T, Spaces'_ft)`, and likewise for finitely presented, flat and proper
morphisms and `Spaces'_{fp, flat, proper}`.

Both are instances of a general statement (`AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor`
is faithful, full and essentially surjective): for a property of morphisms of algebraic spaces
stable under base change and local on the target for the fpqc topology, base change along the
points of `T` is an equivalence. Finite type is stable
under base change (Stacks 03XH) and local on the target (Stacks 041U); finite presentation,
flatness and properness are stable under base change (Stacks 03XR, 03MO, 04WP) and local on the
target (Stacks 041V, 041W, 0422).

## Main results

* `AlgebraicGeometry.SpacesOverSpace.finiteTypeBaseChange_isEquivalence`: **Stacks 0E93**, the
  first equivalence.
* `AlgebraicGeometry.SpacesOverSpace.properFlatBaseChange_isEquivalence`: **Stacks 0E93**, the
  second equivalence.
* `AlgebraicGeometry.SpacesOverSpace.spacesOverSpace_isEquivalence`: **Stacks 0E93**, both.

## Implementation notes

The category on the left of each equivalence has the isomorphisms over `T` as morphisms, being
the core of the category of algebraic spaces over `T` restricted to the morphisms of the given
kind: the category on the right is a groupoid, since `Spaces'_ft` is fibred in groupoids, and a
morphism over `T` which is not an isomorphism does not induce a morphism of `Spaces'_ft`, whose
morphisms are the cartesian squares.

As in Stacks 0D1E, everything is relative to the base scheme `S` of the big fppf site; taking
`S = Spec(ℤ)` recovers the absolute statement.

## References

* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SpacesOverSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : AlgebraicSpaces B S hS)

/-- Being of finite presentation, as a property of morphisms of algebraic spaces over `S`. -/
abbrev finitePresentationProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => Space.IsFinitePresentation B S hS f.hom

/-- Being flat, as a property of morphisms of algebraic spaces over `S`. -/
abbrev flatProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => Space.IsFlat B S hS f.hom

/-- Being of finite presentation, flat and proper, as a property of morphisms of algebraic spaces
over `S`. -/
abbrev properFlatProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  finitePresentationProperty B S hS ⊓ (flatProperty B S hS ⊓ Space.properProperty B S hS)

-- `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` (Stacks 03MO) is a theorem rather than
-- an instance.
attribute [local instance] Space.isFlat_isStableUnderBaseChange

/-- **The functor of Stacks 0E93 for finite type morphisms.** A finite type morphism of
algebraic spaces `X ⟶ T` goes to the functor over the site from the algebraic stack `𝒮_T` of `T`
to `Spaces'_ft` sending a point `(U, t)` of `T` to the base change `U ×_T X ⟶ U`; an isomorphism
over `T` goes to the induced 2-isomorphism. -/
abbrev finiteTypeBaseChange :
    ObjectProperty.FullSubcategory
        (fun X : Core (Over T) => Space.IsFiniteType B S hS X.of.hom.hom) ⥤
      ((Stack.fibredCategory B S hS T.obj).val ⥤ᵇ
        BasedCategory.ofFunctor (cartesianFiniteTypeProjection B S hS)) :=
  baseChangeFunctor (P := Space.finiteTypeProperty B S hS) (T := T)

/-- **The functor of Stacks 0E93 for finitely presented, flat and proper morphisms.** A finitely
presented, flat and proper morphism of algebraic spaces `X ⟶ T` goes to the functor over the site
from `𝒮_T` to `Spaces'_{fp, flat, proper}` sending a point `(U, t)` of `T` to `U ×_T X ⟶ U`. -/
abbrev properFlatBaseChange :
    ObjectProperty.FullSubcategory
        (fun X : Core (Over T) => Space.IsFinitePresentation B S hS X.of.hom.hom ∧
          Space.IsFlat B S hS X.of.hom.hom ∧ Space.IsProper B S hS X.of.hom.hom) ⥤
      ((Stack.fibredCategory B S hS T.obj).val ⥤ᵇ
        BasedCategory.ofFunctor (cartesianProperFlatProjection B S hS)) :=
  baseChangeFunctor (P := properFlatProperty B S hS) (T := T)

/-- **Stacks 0E93**, the first equivalence: finite type morphisms of algebraic spaces `X ⟶ T`,
with isomorphisms over `T`, are equivalent through base change to the functors over the site from
the algebraic stack `𝒮_T` of `T` to the stack `Spaces'_ft` of finite type families of algebraic
spaces. -/
@[stacks 0E93 "the first equivalence: finite type morphisms X ⟶ T and functors 𝒮_T ⟶ Spaces'_ft"]
theorem finiteTypeBaseChange_isEquivalence : (finiteTypeBaseChange B S hS T).IsEquivalence :=
  show (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := Space.finiteTypeProperty B S hS)
    (T := T)).IsEquivalence from ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Stacks 0E93**, the second equivalence: finitely presented, flat and proper morphisms of
algebraic spaces `X ⟶ T`, with isomorphisms over `T`, are equivalent through base change to the
functors over the site from the algebraic stack `𝒮_T` of `T` to the stack
`Spaces'_{fp, flat, proper}` of finitely presented, flat and proper families. -/
@[stacks 0E93 "the second equivalence: finitely presented, flat and proper morphisms X ⟶ T and \
functors 𝒮_T ⟶ Spaces'_{fp, flat, proper}"]
theorem properFlatBaseChange_isEquivalence : (properFlatBaseChange B S hS T).IsEquivalence :=
  show (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := properFlatProperty B S hS)
    (T := T)).IsEquivalence from ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Stacks 0E93.** Base change along the points of an algebraic space `T` gives an equivalence
of finite type morphisms `X ⟶ T` with the functors over the site from `𝒮_T` to `Spaces'_ft`, and an
equivalence of finitely presented, flat and proper morphisms `X ⟶ T` with the functors over the
site from `𝒮_T` to `Spaces'_{fp, flat, proper}`. -/
@[stacks 0E93 "both equivalences"]
theorem spacesOverSpace_isEquivalence :
    (finiteTypeBaseChange B S hS T).IsEquivalence ∧
      (properFlatBaseChange B S hS T).IsEquivalence :=
  ⟨finiteTypeBaseChange_isEquivalence B S hS T, properFlatBaseChange_isEquivalence B S hS T⟩

end AlgebraicGeometry.SpacesOverSpace

end
