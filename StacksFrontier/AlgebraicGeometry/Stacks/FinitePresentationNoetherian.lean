module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# Finiteness over a locally Noetherian algebraic stack (Stacks 0DQJ)

**Stacks 0DQJ** says that over a locally Noetherian target the finiteness conditions on a
1-morphism of algebraic stacks over `S` collapse: a 1-morphism locally of finite type is locally
of finite presentation, and a 1-morphism of finite type and quasi-separated is of finite
presentation.

The local assertion is the source's argument. Local finite type is the universal smooth-diagram
test of **Stacks 06FM** at local finite type of morphisms of algebraic spaces, and local finite
type is smooth local on the source-and-target by **Stacks 06FC**, so the equivalence of
conditions (1) and (2) of Stacks 06FM produces one diagram

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

of algebraic spaces over `f` with `a` smooth and surjective on objects, `b` smooth and `h`
locally of finite type. The right vertical 1-morphism presents `V` as a smooth algebraic-space
chart of `𝒴`, so the universal algebraic-space criterion of **Stacks 04YF** makes `V` locally
Noetherian, and **Stacks 06G4** part (1) upgrades `h` to being locally of finite presentation.
The same diagram then witnesses the existential criterion of Stacks 06FM at local finite
presentation, which is local finite presentation of `f` read backwards across that equivalence.

The global assertion adds nothing: being of finite type is being locally of finite type together
with quasi-compactness (**Stacks 06FS** part (2)) and being of finite presentation is being
locally of finite presentation together with quasi-compactness and quasi-separatedness
(**Stacks 06Q2** part (2)), so the quasi-compactness conjunct is given and the quasi-separatedness
conjunct is a hypothesis.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType`:
  **Stacks 0DQJ**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFinitePresentation_of_isFiniteType`:
  **Stacks 0DQJ**, part (2).

## Implementation notes

Local Noetherianity of an algebraic stack over `S` is not a predicate of its own in this library.
It is the existential smooth-scheme-atlas criterion of **Stacks 04YF**,
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas`, taken at Mathlib's
`AlgebraicGeometry.IsLocallyNoetherian` — which is how **Stacks 04YG** defines it and how the
hypothesis is already phrased for algebraic stacks in
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType`
(**Stacks 06R6**) and `...isLocallyNoetherian_of_isImmersion` (**Stacks 0CPM**). Stacks 04YF is
also what converts it into the universal algebraic-space criterion the proof consumes, since
Stacks 06G4 asks for local Noetherianity of an algebraic space in the form of the étale-local
property `AlgebraicGeometry.Space.HasEtaleLocalProperty` of **Stacks 03E6**.

The source lemma asserts two independent propositions, so the tag's covering set is two
declarations and both keys are registered, as for the sibling permanence statements
**Stacks 06FT**, **Stacks 06FU**, **Stacks 06Q3** and **Stacks 06Q4**.

The two declarations have the same leaf names as the two parts of Stacks 06G4 for morphisms of
*algebraic spaces*
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType`
and `...isFinitePresentation_of_isFiniteType`), which are the facts consumed here; they are
different notions about different objects and are distinguished by namespace exactly as the
composition statements of Stacks 06Q3 are distinguished from their space-level counterparts.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DQJ, part (1).** A 1-morphism of algebraic stacks over `S` which is locally of
finite type and whose target is locally Noetherian is locally of finite presentation. Local
Noetherianity of an algebraic stack over `S` is the smooth-scheme-atlas criterion of
**Stacks 04YG** at `AlgebraicGeometry.IsLocallyNoetherian`.

Local finite type is the universal smooth-diagram test of **Stacks 06FM**, so the equivalence of
its conditions (1) and (2) gives a diagram of algebraic spaces over `f` with smooth vertical
1-morphisms, left vertical 1-morphism surjective on objects, and top horizontal morphism `h`
locally of finite type. The right vertical 1-morphism is a smooth algebraic-space chart of the
target, so its source is locally Noetherian by **Stacks 04YF**, and **Stacks 06G4** part (1)
makes `h` locally of finite presentation; the same diagram read backwards across Stacks 06FM at
local finite presentation is the conclusion. -/
@[stacks 0DQJ "part (1)", sga "3 VIA 2.5.4" "more general"]
theorem isLocallyOfFinitePresentation_of_isLocallyOfFiniteType
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hY : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := by
  -- local Noetherianity is local in the smooth topology, being local in the fppf topology
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  -- every smooth algebraic-space chart of `𝒴` is locally Noetherian, by Stacks 04YF
  have hYchart : Stack.HasPropertyOnEverySpaceChart B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴 :=
    (Stack.exists_space_atlas_iff_forall_space B S hS
        (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1
      ((Stack.exists_scheme_atlas_iff_exists_space_atlas B S hS
        (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1 hY)
  -- a smooth diagram over `f`, whose top horizontal morphism is locally of finite type
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hasu, hb, hh⟩ :=
    (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom).1 hf
  -- `b` presents `V` as a smooth algebraic-space chart of `𝒴`, so `V` is locally Noetherian
  have hbSmooth : IsSmooth B S hS
      (Bicategory.InducedBicategory.mkHom b :
        Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒴.property b hb.1 hb.2
  -- so Stacks 06G4 part (1) upgrades `h` to being locally of finite presentation
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒳.property 𝒴.property f.hom).2
    ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hasu, hb,
      Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hU hV h
        (hYchart V hV _ hbSmooth) hh⟩

/-- **Stacks 0DQJ, part (2).** A 1-morphism of algebraic stacks over `S` which is of finite type
and quasi-separated and whose target is locally Noetherian is of finite presentation.

Being of finite presentation is being locally of finite presentation, quasi-compact and
quasi-separated (**Stacks 06Q2** part (2)) and being of finite type is being locally of finite
type together with quasi-compactness (**Stacks 06FS** part (2)), so only the first conjunct has
content and that is part (1). -/
@[stacks 0DQJ "part (2)"]
theorem isFinitePresentation_of_isFiniteType
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hY : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f)
    (hqs : Stack.AlgebraicStacks.IsQuasiSeparated B S hS f) :
    IsFinitePresentation B S hS f :=
  ⟨isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS f hY hf.1, hf.2, hqs⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
