module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# Composition of finiteness conditions on 1-morphisms of algebraic stacks (Stacks 06FT, 06Q3)

**Stacks 06FT** says that local finite type and finite type of 1-morphisms of algebraic stacks
over `S` are stable under composition, and **Stacks 06Q3** says the same for local finite
presentation and finite presentation.

Both local assertions are **Stacks 06FP** — stability under composition of the existential
smooth-diagram criterion of **Stacks 06FM** — read through the equivalence of conditions (1) and
(2) of Stacks 06FM. The round trip is needed because Stacks 06FS part (1) and Stacks 06Q2
part (1) are defined over the *universal* criterion `HasPropertyOnEverySmoothDiagram`, where
Stacks 06PW inlines the *existential* one; the equivalence between them is exactly what
**Stacks 06FC** at the property in question supplies, and the two finiteness cases of Stacks 06FC
are proved in `StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness`. The composition
hypothesis of Stacks 06FP is **Stacks 03XG** and **Stacks 03XQ** for morphisms of algebraic
spaces.

The two global assertions add the conjuncts of Stacks 06FS part (2) and Stacks 06Q2 part (2):
quasi-compactness, which composes by **Stacks 050W**, and — for finite presentation —
quasi-separatedness, which composes by **Stacks 050K**.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_comp` and
  `...isFiniteType_comp`: **Stacks 06FT**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_comp` and
  `...isFinitePresentation_comp`: **Stacks 06Q3**.

## Implementation notes

Each source lemma asserts two independent propositions — the local one and the global one — so
each tag's covering set is two declarations and both keys are registered.

The four declarations have the same leaf names as the corresponding statements for morphisms of
*algebraic spaces* (`AlgebraicGeometry.Space.isLocallyOfFiniteType_comp`,
`...isFiniteType_comp`, `...isLocallyOfFinitePresentation_comp`, `...isFinitePresentation_comp`).
They are different notions about different objects and are distinguished by namespace exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp` (Stacks 06PX) is distinguished from
`AlgebraicGeometry.Space.isFlat_comp` (Stacks 03MN); the space-level ones are the composition
hypothesis these consume.

## References

* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 06FT -/

/-- Stacks 06FP read through Stacks 06FM: if `P` is smooth local on the source-and-target and
stable under composition, then so is having `P` on every smooth diagram. -/
private theorem hasPropertyOnEverySmoothDiagram_comp_of_isSmoothLocal
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hcomp : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P p → P q → P (p ≫ q))
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : Stack.HasPropertyOnEverySmoothDiagram B S hS P f.hom)
    (hg : Stack.HasPropertyOnEverySmoothDiagram B S hS P g.hom) :
    Stack.HasPropertyOnEverySmoothDiagram B S hS P (f ≫ g).hom :=
  (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
      𝒳.property 𝒵.property (f ≫ g).hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_comp.{u, w} B S hS P hP hcomp
      𝒳.property 𝒴.property 𝒵.property f.hom g.hom
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
        𝒳.property 𝒴.property f.hom).1 hf)
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
        𝒴.property 𝒵.property g.hom).1 hg))

/-- **Stacks 06FT**, the local assertion. The composite of two 1-morphisms of algebraic stacks
over `S` which are locally of finite type is locally of finite type.

Stacks 06FS part (1) is condition (1) of Stacks 06FM at local finite type of morphisms of
algebraic spaces, so this is Stacks 06FP at that property, transported across the equivalence of
conditions (1) and (2) of Stacks 06FM. Local finite type is smooth local on the
source-and-target by **Stacks 06FC** and stable under composition by **Stacks 03XG**. -/
@[stacks 06FT "locally of finite type"]
theorem isLocallyOfFiniteType_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFiniteType B S hS (f ≫ g) :=
  hasPropertyOnEverySmoothDiagram_comp_of_isSmoothLocal B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (fun hU hV hW p q hp hq => Space.isLocallyOfFiniteType_comp B S hS hU hV hW p q hp hq)
    f g hf hg

/-- **Stacks 06FT**, the global assertion. The composite of two finite type 1-morphisms of
algebraic stacks over `S` is of finite type.

Being of finite type is being locally of finite type together with being quasi-compact
(Stacks 06FS, part (2)); the first conjunct composes by the local assertion above and the second
by **Stacks 050W**. -/
@[stacks 06FT "finite type"]
theorem isFiniteType_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsFiniteType B S hS f) (hg : IsFiniteType B S hS g) :
    IsFiniteType B S hS (f ≫ g) :=
  ⟨isLocallyOfFiniteType_comp B S hS f g hf.1 hg.1,
    Stack.isQuasiCompactMorphism_comp B S hS f g hf.2 hg.2⟩

/-! ### Stacks 06Q3 -/

/-- **Stacks 06Q3**, the local assertion. The composite of two 1-morphisms of algebraic stacks
over `S` which are locally of finite presentation is locally of finite presentation.

Stacks 06Q2 part (1) is condition (1) of Stacks 06FM at local finite presentation of morphisms of
algebraic spaces, so this is Stacks 06FP at that property, transported across the equivalence of
conditions (1) and (2) of Stacks 06FM. Local finite presentation is smooth local on the
source-and-target by **Stacks 06FC** and stable under composition by **Stacks 03XQ**. -/
@[stacks 06Q3 "locally of finite presentation"]
theorem isLocallyOfFinitePresentation_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS (f ≫ g) :=
  hasPropertyOnEverySmoothDiagram_comp_of_isSmoothLocal B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (fun hU hV hW p q hp hq => Space.isLocallyOfFinitePresentation_comp B S hS hU hV hW p q hp hq)
    f g hf hg

/-- **Stacks 06Q3**, the global assertion. The composite of two 1-morphisms of algebraic stacks
over `S` of finite presentation is of finite presentation.

Being of finite presentation is being locally of finite presentation together with being
quasi-compact and quasi-separated (Stacks 06Q2, part (2)); the first conjunct composes by the
local assertion above, the second by **Stacks 050W** and the third by **Stacks 050K**. -/
@[stacks 06Q3 "finite presentation"]
theorem isFinitePresentation_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsFinitePresentation B S hS f) (hg : IsFinitePresentation B S hS g) :
    IsFinitePresentation B S hS (f ≫ g) :=
  ⟨isLocallyOfFinitePresentation_comp B S hS f g hf.1 hg.1,
    Stack.isQuasiCompactMorphism_comp B S hS f g hf.2.1 hg.2.1,
    isQuasiSeparated_comp B S hS f g hf.2.2 hg.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
