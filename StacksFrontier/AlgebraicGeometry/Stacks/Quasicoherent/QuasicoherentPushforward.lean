module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsLargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback

/-!
# The quasi-coherent direct image and its higher direct images

**Stacks 077A.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over a base scheme `S`, the
inverse image `f^*` of quasi-coherent modules has a right adjoint

`f_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`,

the **quasi-coherent direct image**, and the **higher direct images** `R^i f_{QCoh,*}` are
obtained by putting the `i`-th higher direct image of modules in its middle slot.  Both are the
source's three-step composite: include the quasi-coherent modules into all modules, take the
direct image there, and come back with the coherator `Q` of **Stacks 0781** part (2).

## Main definitions

* `AlgebraicGeometry.FibredSite.quasicoherentInclusion`: the inclusion
  `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` of **Stacks 06WG** at the section universe the direct images of
  **Stacks 06WE** are constructed in.
* `AlgebraicGeometry.FibredSite.moduleCoheratorSucc`, with
  `AlgebraicGeometry.FibredSite.moduleCoheratorSuccAdjunction` and
  `AlgebraicGeometry.FibredSite.moduleCoheratorSuccCompInclusionIsoId`: the coherator
  `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0781** part (2) at that same section universe.
* `AlgebraicGeometry.Stack.quasicoherentModulePullback`: the inverse image `f^*` of
  **Stacks 06WE** restricted to quasi-coherent modules, which is **Stacks 06WH**.
* `AlgebraicGeometry.Stack.quasicoherentPushforward`: **Stacks 077A**, the quasi-coherent direct
  image `f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.higherDirectImageQuasicoherent`: **Stacks 077A**, the higher direct
  images `R^i f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfQuasicoherentModules`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfQuasicoherentPushforward` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageQuasicoherent`: the same three
  functors for a 1-morphism of the 2-category of algebraic stacks over `S`.

## Main results

* `AlgebraicGeometry.FibredSite.hasTerminal_costructuredArrow_quasicoherentInclusion`: every
  module has a terminal quasi-coherent module mapping to it, at the section universe of the
  direct images.  This is the one existence statement the coherator rests on.
* `AlgebraicGeometry.Stack.quasicoherentPullbackPushforwardAdjunction`: **Stacks 077A**, the
  assertion itself — `f^*` on quasi-coherent modules is left adjoint to `f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.higherDirectImageQuasicoherentZeroIso`:
  `R^0 f_{QCoh,*} = f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageQuasicoherentZeroIso`: the
  second of these for a 1-morphism of algebraic stacks.

## Implementation notes

### The middle slot is `Mod(𝒪)`, not `LQCoh^fbc(𝒪)`

The source composes the inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` with the direct image of
**Stacks 0771** on `LQCoh^fbc` and the coherator of **Stacks 0778**.  Here the middle slot is
all of `Mod(𝒪_𝒳)`: the inclusion is the full subcategory inclusion of **Stacks 06WG**, the
direct image is `AlgebraicGeometry.Stack.moduleSheafPushforward` — **Stacks 06WE** — and the
coherator is the one of **Stacks 0781** part (2), the right adjoint of
`QCoh(𝒪_𝒴) ⊆ Mod(𝒪_𝒴)`.

The two readings give the same functor on the morphisms the source states 077A for.  The
inclusion of `QCoh` into `Mod` factors through `LQCoh^fbc`; for a quasi-compact and
quasi-separated 1-morphism the direct image carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`,
which is **Stacks 0771**; and the coherator of **Stacks 0778** is the restriction of the one of
**Stacks 0781** part (2), both being the right adjoint of an inclusion of `QCoh(𝒪_𝒴)` built as
`A ↦ (⊤_ CostructuredArrow i A).left` — this is what
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean` records when it builds the
two coherators from one existence theorem.

Routing through `Mod(𝒪)` is what makes the result *unconditional in the 1-morphism*: no
quasi-compactness and no quasi-separatedness appear below.  The source spends those two
hypotheses only on **Stacks 0771**, to know that the middle functor preserves the smaller
category `LQCoh^fbc`, and that question does not arise when the middle category is all of
`Mod(𝒪)`.  So the adjunction and the higher direct images are available for every 1-morphism,
and specialise to the source's statement.

It is also what makes the result available at all at this seating.  `LQCoh^fbc(𝒪_𝒳)` is pinned
to the section universe `u` of the schemes — the comparison map of **Stacks 06WC** pins it, see
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSmoothLocal.lean` — whereas the
direct image of **Stacks 06WE** along a 1-morphism of algebraic stacks is computed by limits
indexed by the two sites and so lives at section universe `u + 1`.  There is therefore no
`LQCoh^fbc(𝒪_𝒳)` in this library in the universe the direct image produces, and no composite to
form there.  `QCoh(𝒪_𝒳)` has no such obstruction: it is a full subcategory of the modules, in
whatever section universe they are taken.

### The coherator at section universe `u + 1`

`AlgebraicGeometry.FibredSite.moduleCoherator` is the coherator at section universe `u`, for the
same reason.  `AlgebraicGeometry.FibredSite.moduleCoheratorSucc` below is the same construction
at `u + 1`, where the direct image lives: the special adjoint functor theorem applied to the
inclusion of **Stacks 06WG**, in the form that exhibits the right adjoint rather than the form
that merely asserts one exists.  Its colimit inputs are the ones the file
`QuasicoherentColimitsLargeModuleUniverse.lean`, in the directory
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/`,
provides — the existence of colimits of `QCoh(𝒪_𝒳)` and their preservation by the inclusion,
which is **Stacks 06WN** part (1) — and the index universe of the theorem is `u + 1` as well,
the universe of the morphisms of `QCoh(𝒪_𝒳)` at this section universe.  Local smallness is
therefore automatic and is not a hypothesis, unlike at section universe `u`.

### What is carried, and why

Three inputs are hypotheses, and all three are inputs of **Stacks 0781** part (1) as this
library has it.  None of them is the conclusion of **Stacks 077A** or yields it: each is a
statement about `QCoh(𝒪_𝒴)` alone, mentioning neither the 1-morphism nor any direct image.

*Closure of quasi-coherence under colimits* (`hclosed`,
`AlgebraicGeometry.FibredSite.QuasicoherentClosedUnderColimitsSucc`) is the mathematical half of
**Stacks 06WN** part (1), the hypothesis of
`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_largeModuleUniverse` and of
`AlgebraicGeometry.FibredSite.preservesColimits_quasicoherentInclusion`.

*Well-copoweredness* (`hwp`) and *a separator* (`hsep`) are the two remaining conditions of the
special adjoint functor theorem, and the source draws both from **Stacks 0781** part (1).  The
separator is the substantive one: the source produces it from a smooth groupoid presentation
`𝒳 = [U/R]`, and neither that presentation argument nor the abelian structure on `QCoh(𝒪_𝒳)` is
in this library, so part (1) itself is only available over them — compare
`AlgebraicGeometry.FibredSite.isGrothendieckAbelian_quasicoherentModules`.

No abelian structure on `QCoh(𝒪_𝒴)` is needed or assumed: the higher direct images are the right
derived functors of the direct image of *modules*, whose abelian structure and enough injectives
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` supplies, and the coherator is applied to
them afterwards.

### What is not here

The source closes 077A by asserting that `{R^i f_{QCoh,*}}_{i ≥ 0}` is a cohomological
δ-functor.  That assertion is not made below.  Its connecting maps and long exact sequences come
from the ones of `R^i f_*` on `Mod(𝒪_𝒳)` by applying `Q`, and for them to stay exact one needs
`QCoh(𝒪_𝒴)` to be abelian and `Q` to be exact; the first is an instance-implicit hypothesis
everywhere in this area and the second is **Stacks 0779**, which this library does not have — see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherentCohomology.lean`, which
carry exactly that kernel computation as a hypothesis `hQker`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` of the quasi-coherent modules of **Stacks 06WG** into
all modules on the associated fppf site, at the section universe `u + 1` in which the direct
images of **Stacks 06WE** along a 1-morphism of algebraic stacks are constructed. -/
abbrev quasicoherentInclusion :
    quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp ⥤
      SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp .fppf) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
    (ringStructureSheafCore B S hS p hp .fppf)).ι

/-- **Closure of quasi-coherence under colimits at section universe `u + 1`**, the mathematical
half of **Stacks 06WN** part (1) in the universe the direct images of **Stacks 06WE** produce.
This is the hypothesis of
`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_largeModuleUniverse`. -/
abbrev QuasicoherentClosedUnderColimitsSucc : Prop :=
  ∀ (K : Type (u + 1)) [Category.{u + 1} K],
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K

/-- **Every module has a terminal quasi-coherent module mapping to it**, at section universe
`u + 1`, provided quasi-coherence is closed under colimits there and `QCoh(𝒪_𝒳)` is
well-copowered with a separator.  This is the special adjoint functor theorem
`CategoryTheory.Limits.hasTerminal_of_isSeparating`, applied at the index universe `u + 1` of the
morphisms of `QCoh(𝒪_𝒳)`, in the form that exhibits the right adjoint of the inclusion as
`A ↦ (⊤_ CostructuredArrow i A).left`.

Local smallness, a hypothesis of
`AlgebraicGeometry.FibredSite.hasTerminal_costructuredArrow_of_quasicoherentModules` at section
universe `u`, is automatic here: the index universe is the universe of the morphisms. -/
theorem hasTerminal_costructuredArrow_quasicoherentInclusion
    (hclosed : QuasicoherentClosedUnderColimitsSucc B S hS p hp)
    (hwp : WellPowered.{u + 1} (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp))
    (A : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp .fppf)) :
    HasTerminal (CostructuredArrow (quasicoherentInclusion B S hS p hp) A) :=
  letI := hasColimits_quasicoherentModules_largeModuleUniverse.{u, u + 1, u, u} B S hS p hp hclosed
  letI := preservesColimits_quasicoherentInclusion.{u, u + 1, u, u} B S hS p hp hclosed
  letI := hwp
  letI := hsep
  letI := hasFiniteColimits_of_hasColimitsOfSize
    (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)
  letI := PreservesColimitsOfSize.preservesFiniteColimits (quasicoherentInclusion B S hS p hp)
  hasTerminal_of_isSeparating.{u + 1}
    (CostructuredArrow.isSeparating_inverseImage_proj (quasicoherentInclusion B S hS p hp) A
      (isSeparator_separator (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)))

/-- **Stacks 0781, part (2), at section universe `u + 1`: the coherator on `Mod(𝒪_𝒳)`.**  The
right adjoint of the inclusion of `QCoh(𝒪_𝒳)` into all modules on the associated fppf site: it
sends a module `A` to the terminal quasi-coherent module equipped with a map to `A`.

`AlgebraicGeometry.FibredSite.moduleCoherator` is the same construction at section universe `u`;
`u + 1` is the universe the direct images of **Stacks 06WE** along a 1-morphism of algebraic
stacks live in, and so the universe **Stacks 077A** needs the coherator in. -/
@[stacks 0781 "part (2): the coherator Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳), at section universe u + 1"]
def moduleCoheratorSucc
    (hclosed : QuasicoherentClosedUnderColimitsSucc B S hS p hp)
    (hwp : WellPowered.{u + 1} (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)) :
    SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp :=
  letI := fun A => hasTerminal_costructuredArrow_quasicoherentInclusion B S hS p hp
    hclosed hwp hsep A
  rightAdjointOfCostructuredArrowTerminals (quasicoherentInclusion B S hS p hp)

/-- **Stacks 0781, part (2): the coherator is right adjoint to the inclusion.**  The adjunction
is the universal property of the terminal objects the coherator is built from. -/
@[stacks 0781 "part (2): the adjunction between the inclusion and the coherator, at section \
  universe u + 1"]
def moduleCoheratorSuccAdjunction
    (hclosed : QuasicoherentClosedUnderColimitsSucc B S hS p hp)
    (hwp : WellPowered.{u + 1} (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)) :
    quasicoherentInclusion B S hS p hp ⊣ moduleCoheratorSucc B S hS p hp hclosed hwp hsep :=
  letI := fun A => hasTerminal_costructuredArrow_quasicoherentInclusion B S hS p hp
    hclosed hwp hsep A
  adjunctionOfCostructuredArrowTerminals (quasicoherentInclusion B S hS p hp)

/-- **Stacks 0781, part (2): the coherator fixes the quasi-coherent modules.**  The inclusion is
fully faithful, so the unit of the adjunction is an isomorphism; this is the source's assertion
that `Q 𝓕 → 𝓕` is an isomorphism for quasi-coherent `𝓕`. -/
@[stacks 0781 "part (2): the coherator composed with the inclusion is the identity, at section \
  universe u + 1"]
def moduleCoheratorSuccCompInclusionIsoId
    (hclosed : QuasicoherentClosedUnderColimitsSucc B S hS p hp)
    (hwp : WellPowered.{u + 1} (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp)) :
    quasicoherentInclusion B S hS p hp ⋙ moduleCoheratorSucc B S hS p hp hclosed hwp hsep ≅
      𝟭 (quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp) :=
  (asIso (moduleCoheratorSuccAdjunction B S hS p hp hclosed hwp hsep).unit).symm

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

/-- The associated fppf site of a category fibred in groupoids whose objects lie in `Type (u + 1)`
and whose morphisms lie in `Type u` admits sheafification of abelian sheaves at section universe
`u + 1`: the site is essentially small there, so sheafification transports from a small model.

This is one of the two conditions under which the direct images of **Stacks 06WE** and their right
derived functors are constructed at this seating. -/
theorem hasSheafify_fppfAssociatedTopology_succ :
    HasSheafify (associatedTopology B S hS p B.topology) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- The associated fppf site of a category fibred in groupoids whose objects lie in `Type (u + 1)`
and whose morphisms lie in `Type u` has the property that the local isomorphisms of abelian
sheaves at section universe `u + 1` are the locally bijective morphisms, for the same reason.

This is the second of those two conditions. -/
theorem wEqualsLocallyBijective_fppfAssociatedTopology_succ :
    (associatedTopology B S hS p B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance]
  hasSheafify_fppfAssociatedTopology_succ wEqualsLocallyBijective_fppfAssociatedTopology_succ

include hp hq f hf

/-- The direct image `f_*` of **Stacks 06WE** on modules on the associated fppf sites, at section
universe `u + 1`. -/
abbrev fppfModuleSheafPushforward :
    SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS q hq .fppf) :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl

/-- The higher direct image `R^i f_*` of modules on the associated fppf sites, at section universe
`u + 1`: the `i`-th right derived functor of `AlgebraicGeometry.Stack.moduleSheafPushforward`. -/
abbrev fppfModuleSheafHigherDirectImage (i : ℕ) :
    SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS q hq .fppf) :=
  moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl i

/-- **Stacks 06WH.** The inverse image `f^*` of **Stacks 06WE** restricted to quasi-coherent
modules: the inverse image of a quasi-coherent module is quasi-coherent, so the composite of the
inclusion of **Stacks 06WG** with `f^*` lifts to the full subcategory `QCoh(𝒪_𝒳)`. -/
def quasicoherentModulePullback :
    FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS q hq ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp :=
  ObjectProperty.lift _
    (FibredSite.quasicoherentInclusion B S hS q hq ⋙
      modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl)
    fun M => by
      exact @isQuasicoherentOnSite_modulePullback.{u, u + 1, u, u} B S hS _ _ _ _
        p q hp hq f hf M.obj M.property

/-- The inverse image of quasi-coherent modules is the inverse image of all modules: the lift of
**Stacks 06WH** composed with the inclusion of **Stacks 06WG** is the inclusion followed by
`f^*`. -/
def quasicoherentModulePullbackCompInclusionIso :
    quasicoherentModulePullback B S hS p q hp hq f hf ⋙
        FibredSite.quasicoherentInclusion B S hS p hp ≅
      FibredSite.quasicoherentInclusion B S hS q hq ⋙
        modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl :=
  ObjectProperty.liftCompιIso _ _ _

section Quasicoherent

variable (hclosed : FibredSite.QuasicoherentClosedUnderColimitsSucc B S hS q hq)
  (hwp : WellPowered.{u + 1}
    (FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS q hq)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS q hq))

include hclosed hwp hsep

/-- **Stacks 077A: the quasi-coherent direct image `f_{QCoh,*}`.**  Include the quasi-coherent
modules of `𝒳` into all modules on its associated fppf site, take the direct image of
**Stacks 06WE**, and come back with the coherator of **Stacks 0781** part (2).

The source's middle slot is the direct image of **Stacks 0771** on `LQCoh^fbc(𝒪_𝒳)` and its
coherator is the one of **Stacks 0778**; the two readings agree on the quasi-compact and
quasi-separated 1-morphisms the source states 077A for, and this one needs neither hypothesis.
See the implementation notes. -/
@[stacks 077A "f_{QCoh,*} as the composite of the inclusion of Stacks 06WG, the direct image of \
  Stacks 06WE on all modules, and the coherator of Stacks 0781 part (2); the coherator's three \
  special-adjoint-functor-theorem inputs from Stacks 0781 part (1) are carried as the named \
  hypotheses hclosed, hwp, hsep"]
def quasicoherentPushforward :
    FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS q hq :=
  FibredSite.quasicoherentInclusion B S hS p hp ⋙
    fppfModuleSheafPushforward B S hS p q hp hq f hf ⋙
      FibredSite.moduleCoheratorSucc B S hS q hq hclosed hwp hsep

/-- **Stacks 077A: the higher direct images `R^i f_{QCoh,*}`.**  The composite defining
`f_{QCoh,*}` with the `i`-th higher direct image of modules in its middle slot. -/
@[stacks 077A "R^i f_{QCoh,*} as the same composite with the i-th higher direct image of modules \
  in the middle slot; the coherator's three inputs from Stacks 0781 part (1) are carried as the \
  named hypotheses hclosed, hwp, hsep"]
def higherDirectImageQuasicoherent (i : ℕ) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS p hp ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS q hq :=
  FibredSite.quasicoherentInclusion B S hS p hp ⋙
    fppfModuleSheafHigherDirectImage B S hS p q hp hq f hf i ⋙
      FibredSite.moduleCoheratorSucc B S hS q hq hclosed hwp hsep

/-- **Stacks 077A, the assertion itself: `f^*` on quasi-coherent modules has the right adjoint
`f_{QCoh,*}`.**

The adjunction `f^* ⊣ f_*` of **Stacks 06WE** composed with the coherator adjunction of
**Stacks 0781** part (2) is an adjunction between `QCoh(𝒪_𝒴)` and all of `Mod(𝒪_𝒳)`; restricting
it along the fully faithful inclusion of `QCoh(𝒪_𝒳)`, which is possible because `f^*` preserves
quasi-coherence by **Stacks 06WH**, is the asserted adjunction. -/
@[stacks 077A "the assertion: the inverse image of quasi-coherent modules is left adjoint to \
  f_{QCoh,*}; the coherator's three inputs from Stacks 0781 part (1) are carried as the named \
  hypotheses hclosed, hwp, hsep"]
def quasicoherentPullbackPushforwardAdjunction :
    quasicoherentModulePullback B S hS p q hp hq f hf ⊣
      quasicoherentPushforward B S hS p q hp hq f hf hclosed hwp hsep :=
  Adjunction.restrictFullyFaithful
    ((FibredSite.moduleCoheratorSuccAdjunction B S hS q hq hclosed hwp hsep).comp
      (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u}
        B S hS p q hp hq f hf B.topology le_rfl))
    (Functor.FullyFaithful.id _)
    (ObjectProperty.fullyFaithfulι _)
    ((quasicoherentModulePullbackCompInclusionIso B S hS p q hp hq f hf).symm)
    (Iso.refl _)

/-- **`R^0 f_{QCoh,*} = f_{QCoh,*}`.**  The direct image of modules is a right adjoint, hence
left exact, so its zeroth right derived functor is itself; the composite with the inclusion and
the coherator inherits the identification. -/
def higherDirectImageQuasicoherentZeroIso :
    higherDirectImageQuasicoherent B S hS p q hp hq f hf hclosed hwp hsep 0 ≅
      quasicoherentPushforward B S hS p q hp hq f hf hclosed hwp hsep :=
  Functor.isoWhiskerLeft (FibredSite.quasicoherentInclusion B S hS p hp)
    (Functor.isoWhiskerRight
      (moduleSheafHigherDirectImageZeroIso.{u, u + 1, u, u + 1, u}
        B S hS p q hp hq f hf B.topology le_rfl)
      (FibredSite.moduleCoheratorSucc B S hS q hq hclosed hwp hsep))

end Quasicoherent

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `QCoh(𝒪_𝒳)`, the quasi-coherent modules of **Stacks 06WG** on the fppf site of an algebraic
stack `𝒳` over `S`, at the section universe `u + 1` in which the direct images of **Stacks 06WE**
and their right derived functors are constructed at this seating.  It is the full subcategory of
`Mod(𝒪_𝒳)` at that section universe cut out by quasi-coherence. -/
abbrev fppfQuasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :=
  FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ 𝒴)
  (hclosed : FibredSite.QuasicoherentClosedUnderColimitsSucc B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids)
  (hwp : WellPowered.{u + 1} (fppfQuasicoherentModules B S hS 𝒴)ᵒᵖ)
  (hsep : HasSeparator (fppfQuasicoherentModules B S hS 𝒴))

/-- **Stacks 06WH** for a 1-morphism of algebraic stacks: the inverse image `g^*` of
**Stacks 06WE** restricted to quasi-coherent modules.

The source is seated at its own structure functor: by clause (2) of **Stacks 02XS**, the functor
underlying `g` composed with the structure functor of the target *equals* the structure functor of
the source, which is the strictness the inverse image asks for. -/
abbrev fppfQuasicoherentModulePullback :
    fppfQuasicoherentModules B S hS 𝒴 ⥤ fppfQuasicoherentModules B S hS 𝒳 :=
  quasicoherentModulePullback B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)

/-- **Stacks 077A for a 1-morphism of algebraic stacks: the quasi-coherent direct image
`g_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`.** -/
@[stacks 077A "g_{QCoh,*} for a 1-morphism of algebraic stacks over S; the coherator's three \
  inputs from Stacks 0781 part (1) are carried as the named hypotheses hclosed, hwp, hsep"]
abbrev fppfQuasicoherentPushforward :
    fppfQuasicoherentModules B S hS 𝒳 ⥤ fppfQuasicoherentModules B S hS 𝒴 :=
  quasicoherentPushforward B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) hclosed hwp hsep

/-- **Stacks 077A for a 1-morphism of algebraic stacks: the higher direct images
`R^i g_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`.**  This is the higher direct image of modules on the
fppf sites, the `Rⁱf_*` of **Stacks 0770**, read in `QCoh(𝒪_𝒴)` rather than in all of
`Mod(𝒪_𝒴)`. -/
@[stacks 077A "R^i g_{QCoh,*} for a 1-morphism of algebraic stacks over S; the coherator's three \
  inputs from Stacks 0781 part (1) are carried as the named hypotheses hclosed, hwp, hsep"]
abbrev fppfHigherDirectImageQuasicoherent (i : ℕ) :
    fppfQuasicoherentModules B S hS 𝒳 ⥤ fppfQuasicoherentModules B S hS 𝒴 :=
  higherDirectImageQuasicoherent B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) hclosed hwp hsep i

/-- **`R^0 g_{QCoh,*} = g_{QCoh,*}`** for a 1-morphism of algebraic stacks. -/
abbrev fppfHigherDirectImageQuasicoherentZeroIso :
    fppfHigherDirectImageQuasicoherent B S hS g hclosed hwp hsep 0 ≅
      fppfQuasicoherentPushforward B S hS g hclosed hwp hsep :=
  higherDirectImageQuasicoherentZeroIso B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) hclosed hwp hsep

end AlgebraicGeometry.Stack.AlgebraicStacks

end
