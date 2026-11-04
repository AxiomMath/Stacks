module

public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSerreSubcategory

/-!
# The derived category with quasi-coherent cohomology on an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` in a big fppf site.  Inside the category
`Mod(𝒪_𝒳)` of modules on the associated fppf site sit two full subcategories: the locally
quasi-coherent modules with the flat base change property (**Stacks 06WJ** and **Stacks 0762**,
tested after restriction to the associated étale site), written `LQCoh^fbc(𝒪_𝒳)`, and the
parasitic modules of **Stacks 0773**.  Passing to complexes, `D_{LQCoh^fbc}(𝒪_𝒳)` is the full
subcategory of `D(𝒪_𝒳)` of complexes all of whose cohomology modules are in `LQCoh^fbc(𝒪_𝒳)`,
and `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is the full subcategory of complexes whose cohomology
modules are in both.

**Stacks 07B6** defines the *derived category of `𝒪_𝒳`-modules with quasi-coherent cohomology
sheaves* as the Verdier quotient

`D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

That quotient is formed here as the localization of `D_{LQCoh^fbc}(𝒪_𝒳)` at the class of
morphisms whose cone lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, which is the construction of a
Verdier quotient.

## Main definitions

* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChange`: the subcategory
  `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChange`: the subcategory
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedQuasicoherentW`: the morphisms of `D_{LQCoh^fbc}(𝒪_𝒳)` whose
  cone is in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, the class the Verdier quotient inverts.
* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherent`: **Stacks 07B6**, the category
  `D_QCoh(𝒪_𝒳)`, with `AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherent` the quotient
  functor out of `D_{LQCoh^fbc}(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW`: once `D_{LQCoh^fbc}(𝒪_𝒳)` is a
  triangulated subcategory, the inverted class is exactly the class attached to the
  subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`; this is what makes
  the localization the Verdier quotient by that subcategory and not merely a localization.
* `AlgebraicGeometry.Stack.inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange`:
  inside `D_{LQCoh^fbc}(𝒪_𝒳)` the condition of lying in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is
  just that the cohomology modules are parasitic, the local quasi-coherence being automatic.

## Implementation notes

The cone of a morphism is taken in the ambient derived category `D(𝒪_𝒳)`, so the inverted class
is `CategoryTheory.MorphismProperty.inverseImage` of the class attached to
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` along the inclusion of `D_{LQCoh^fbc}(𝒪_𝒳)`.  This is
available with no hypothesis on `D_{LQCoh^fbc}(𝒪_𝒳)`, and it agrees with the class computed
inside `D_{LQCoh^fbc}(𝒪_𝒳)` as soon as the latter is triangulated, which is
`AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW`.  The triangulated property of
`D_{LQCoh^fbc}(𝒪_𝒳)` (**Stacks 0771**) is an input this library does not yet have, which is why
that agreement is stated over it rather than used in the definition.  The weak Serre property of
the parasitic modules (**Stacks 0774** (2)) is no longer such an input:
`AlgebraicGeometry.Stack.isSerreClass_parasiticModules` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSheafification.lean` proves it.

Being abelian and having a derived category are hypotheses on `Mod(𝒪_𝒳)` rather than
constructions: the abelian structure of module sheaves on the associated fppf site needs the
site to be essentially small, and the derived category needs a choice of localization universe.

The module universe is the universe `u` of the schemes throughout, since
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` pins it there.  Both the
locally quasi-coherent and the flat base change conditions are conditions on the restriction of
a module to the associated étale site; the underlying presheaf of rings of the structure sheaf
is the same for all five topologies of **Stacks 06TP**, so the restriction leaves the presheaf
of modules unchanged and the conditions can be read directly off an fppf module.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The category `Mod(𝒪_𝒳)` of modules on the fppf site associated with an algebraic stack. -/
abbrev fppfModules :=
  SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf)

/-- The subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`: a module on the fppf site of an algebraic
stack belongs to it when its restriction to the associated étale site is locally quasi-coherent
(**Stacks 06WJ**) and has the flat base change property (**Stacks 0762**).  Restriction changes
neither the presheaf of modules nor the presheaf of rings it is a module over, so the condition
is tested on the same underlying presheaf of modules. -/
abbrev locallyQuasicoherentFlatBaseChangeFppfModules :
    ObjectProperty (fppfModules B S hS 𝒳) :=
  fun F => IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.val

variable [Abelian (fppfModules B S hS 𝒳)] [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

/-- The subcategory `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` of complexes of modules on the fppf site of
an algebraic stack all of whose cohomology modules are locally quasi-coherent with the flat base
change property. -/
abbrev derivedLocallyQuasicoherentFlatBaseChange :
    ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳)

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` of complexes of modules on the
fppf site of an algebraic stack all of whose cohomology modules are parasitic (**Stacks 0773**)
*and* locally quasi-coherent with the flat base change property. -/
abbrev derivedParasiticLocallyQuasicoherentFlatBaseChange :
    ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (parasiticModules B S hS 𝒳 .fppf ⊓
      locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳)

/-- The class of morphisms of `D_{LQCoh^fbc}(𝒪_𝒳)` which the Verdier quotient of **Stacks 07B6**
inverts: those whose cone lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.  The cone is taken in the
ambient derived category `D(𝒪_𝒳)`. -/
abbrev derivedQuasicoherentW :
    MorphismProperty
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  MorphismProperty.inverseImage
    (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).trW
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι

/-- **Stacks 07B6.** The *derived category of `𝒪_𝒳`-modules with quasi-coherent cohomology
sheaves* of an algebraic stack `𝒳`, that is the Verdier quotient

`D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`,

realized as the localization of `D_{LQCoh^fbc}(𝒪_𝒳)` at the morphisms whose cone lies in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 07B6 "the Verdier quotient D_QCoh(𝒪_𝒳) = D_LQCoh^fbc(𝒪_𝒳) / D_(Parasitic ∩ \
  LQCoh^fbc)(𝒪_𝒳)"]
abbrev derivedCategoryQuasicoherent := (derivedQuasicoherentW B E h S hS 𝒳).Localization

/-- **Stacks 07B6**, the quotient functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` of the Verdier
quotient. -/
@[stacks 07B6 "the quotient functor onto D_QCoh(𝒪_𝒳)"]
abbrev toDerivedCategoryQuasicoherent :
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory ⥤
      derivedCategoryQuasicoherent B E h S hS 𝒳 :=
  (derivedQuasicoherentW B E h S hS 𝒳).Q

/-- A morphism of `D_{LQCoh^fbc}(𝒪_𝒳)` is inverted by the Verdier quotient exactly when its cone
in `D(𝒪_𝒳)` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedQuasicoherentW_iff
    {X Y : (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory}
    (f : X ⟶ Y) :
    derivedQuasicoherentW B E h S hS 𝒳 f ↔
      (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).trW
        ((derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι.map f) :=
  Iff.rfl

/-- Inside `D_{LQCoh^fbc}(𝒪_𝒳)`, lying in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is the same as having
parasitic cohomology modules: the local quasi-coherence and flat base change halves hold for
every object of `D_{LQCoh^fbc}(𝒪_𝒳)` already. -/
theorem inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange :
    (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).inverseImage
        (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι =
      (DerivedCategoryB.derivedCategoryB
          (parasiticModules B S hS 𝒳 .fppf)).inverseImage
        (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι := by
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff]
  exact ⟨fun hX n => (hX n).1, fun hX n => ⟨hX n, X.property n⟩⟩

/-- **The localization of Stacks 07B6 is the Verdier quotient by
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.**  Once `D_{LQCoh^fbc}(𝒪_𝒳)` is a triangulated subcategory of
`D(𝒪_𝒳)`, a cone computed in `D(𝒪_𝒳)` of a morphism of `D_{LQCoh^fbc}(𝒪_𝒳)` is the image of a
cone computed in `D_{LQCoh^fbc}(𝒪_𝒳)`, so the inverted class is the class attached to the
subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedQuasicoherentW_eq_trW
    [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
    [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
      𝒳).IsClosedUnderIsomorphisms] :
    derivedQuasicoherentW B E h S hS 𝒳 =
      ((derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).inverseImage
        (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι).trW := by
  ext X Y f
  exact ((derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).inverseImage_trW_iff
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι f).symm

end AlgebraicGeometry.Stack

end
