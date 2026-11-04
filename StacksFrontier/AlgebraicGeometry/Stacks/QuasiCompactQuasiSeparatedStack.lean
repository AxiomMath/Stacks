module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource

/-!
# Morphisms out of quasi-compact and quasi-separated algebraic stacks (Stacks 075S)

Stacks 075S has three parts, for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks: if `𝒳` is
quasi-compact and `𝒴` is quasi-separated then `f` is quasi-compact (part (1)); if moreover `𝒳` is
quasi-separated then `f` is quasi-compact and quasi-separated (part (2)); and a fibre product of
quasi-compact and quasi-separated algebraic stacks is quasi-compact and quasi-separated
(part (3)).

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack`: **Stacks 075S**,
  part (1).
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_and_isQuasiSeparated`: **Stacks 075S**,
  part (2).
* `AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`:
  **Stacks 075S**, part (3).

## The hypothesis on the base scheme

The source states Stacks 075S absolutely, i.e. over `Spec ℤ`, and its proof of part (1) is
Stacks 050Y applied to `𝒳 ⟶ 𝒴 ⟶ Spec ℤ`, which needs the structure morphism of the quasi-compact
`𝒳` to be quasi-compact. Over a general base scheme `S` that step is **false**: a surjective
smooth presentation of a quasi-compact algebraic stack is by an affine object `V` of the site, the
base change of the structure morphism of `V` by an affine `W` is the product `W ×_S V` taken in
the site, and for a base scheme which is not quasi-separated two affine opens can meet in a
non-quasi-compact open. So the three statements carry the hypothesis `QuasiSeparatedSpace S`,
which `Spec ℤ` satisfies, being affine; at `S = Spec ℤ` they are exactly the source's statements.

The separation conditions are read over the base, `AlgebraicGeometry.Stack.IsQuasiSeparatedOver`
(**Stacks 050D**, part (4)), which at `S = Spec ℤ` is absolute quasi-separatedness
(**Stacks 050D**, part (8)). Over a general base, a hypothesis of absolute quasi-separatedness is
carried to the over-the-base form by
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`, and
the over-the-base conclusion of part (3) is carried back to the absolute one by Stacks 050N
part (8) at the projection followed by Stacks 050L part (8),
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`.

## Implementation notes

Quasi-compactness of the structure morphism of a quasi-compact algebraic stack is reached from
the represented case `AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_schemeStack`
through **Stacks 050X**, the presentation being surjective and its composite with the structure
morphism of `𝒳` being the structure morphism of the presenting object on the nose.

The converse direction, `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isQuasiCompactMorphism`,
replaces the source's appeal to Stacks 050W: the base change of a quasi-compact 1-morphism along
the identity of its target is a 2-fibre product which surjects onto the source, by Stacks 04ZU at
the surjective identity, so a quasi-compact 1-morphism into a quasi-compact algebraic stack has
quasi-compact source with no product over the final stack formed.

## References

* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The terminal object of the big fppf site over `S` has underlying scheme `S`**, so its
underlying space is quasi-separated as soon as `S` is. -/
theorem quasiSeparatedSpace_toScheme_terminal (hqs : QuasiSeparatedSpace S) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))) := by
  have e : (BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS)) ≅ S :=
    (BigFppfOver.toScheme B S hS).mapIso
      (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := B.obj hS)))
  exact (quasiSeparatedSpace_congr (Scheme.homeoOfIso e)).2 hqs

/-- **The product in the big fppf site over a quasi-separated base of two objects with compact
underlying space has compact underlying space.** The product is a fibre product over the terminal
object, whose underlying scheme is `S`; the second structure morphism is quasi-compact because its
source is compact and `S` is quasi-separated, quasi-compactness of morphisms of schemes is stable
under base change, and the canonical functor to schemes preserves fibre products. -/
theorem compactSpace_prod_of_quasiSeparatedSpace (V T : BigFppfOver B S hS)
    (hqs : QuasiSeparatedSpace S)
    (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (V ⨯ T)) := by
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hPB : IsPullback (Limits.prod.fst : V ⨯ T ⟶ V) Limits.prod.snd
      (terminal.from V) (terminal.from T) := IsPullback.of_hasBinaryProduct' V T
  have hterm := quasiSeparatedSpace_toScheme_terminal B S hS hqs
  have _ := hT
  have hqcT : QuasiCompact ((BigFppfOver.toScheme B S hS).map (terminal.from T)) :=
    inferInstance
  have hqcfst : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (Limits.prod.fst : V ⨯ T ⟶ V)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hPB.flip.map (BigFppfOver.toScheme B S hS)) hqcT
  have _ := hV
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (Limits.prod.fst : V ⨯ T ⟶ V))

/-- **The structure morphism of a quasi-compact algebraic stack over a quasi-separated base is
quasi-compact in the sense of Stacks 050U.**

Stacks 04YC gives a surjective smooth presentation `a : 𝒰 ⟶ 𝒳` by an affine object `V` of the
site, whose own structure morphism is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_schemeStack`, the products
`W ×_S V` with affine objects being compact over a quasi-separated base. That structure morphism
is `a` followed by the structure morphism of `𝒳`, so Stacks 050X descends quasi-compactness along
the surjection `a`. -/
theorem isQuasiCompactMorphism_structureMorphism (hqs : QuasiSeparatedSpace S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    IsQuasiCompactMorphism.{u, w} B S hS (structureMorphism.{u, w} B S hS 𝒳) := by
  obtain ⟨V, hV, a, hasurj, -⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h𝒳
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  have hV' : IsQuasiCompactMorphism.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V)) := by
    refine isQuasiCompactMorphism_structureMorphism_schemeStack.{u, w} B S hS V fun W hW => ?_
    have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hW
    exact compactSpace_prod_of_quasiSeparatedSpace B S hS W V hqs inferInstance inferInstance
  exact isQuasiCompactMorphism_of_comp_of_isSurjective B S hS a
    (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V))
    (structureMorphism.{u, w} B S hS 𝒳)
    (@eqToIso _ (Bicategory.homCategory _ _) _ _ (comp_structureMorphism.{u, w} B S hS a))
    hasurj hV'

/-- **The source of a quasi-compact 1-morphism into a quasi-compact algebraic stack is
quasi-compact.** The base change of the 1-morphism along the identity of its target is a 2-fibre
product which is quasi-compact by hypothesis and which surjects onto the source, by Stacks 04ZU
applied to the surjective identity. -/
theorem isQuasiCompactStack_of_isQuasiCompactMorphism
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism.{u, w} B S hS f)
    (h𝒴 : IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  isQuasiCompactStack_of_isSurjective B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f).snd (hf 𝒴 (𝟙 𝒴) h𝒴)
    (isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f)
      (isSurjective_id.{u, w} B S hS 𝒴))

/-- **Stacks 075S, part (1).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over a
quasi-separated base scheme with `𝒳` quasi-compact and `𝒴` quasi-separated over the base is
quasi-compact.

The structure morphism of `𝒳` is `f` followed by the structure morphism of `𝒴`, and it is
quasi-compact because `𝒳` is; the structure morphism of `𝒴` is quasi-separated because `𝒴` is
quasi-separated over the base; so Stacks 050Y cancels it. -/
@[stacks 075S "part (1)", sga "4 VI 1.14" "(i), algebraic stacks"]
theorem isQuasiCompactMorphism_of_isQuasiCompactStack (hqs : QuasiSeparatedSpace S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒴 : IsQuasiSeparatedOver.{u, w} B S hS 𝒴) :
    IsQuasiCompactMorphism.{u, w} B S hS f := by
  refine isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS f
    (structureMorphism.{u, w} B S hS 𝒴) ?_ h𝒴
  rw [comp_structureMorphism.{u, w} B S hS f]
  exact isQuasiCompactMorphism_structureMorphism B S hS hqs 𝒳 h𝒳

/-- **Stacks 075S, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over a
quasi-separated base scheme with `𝒳` quasi-compact and quasi-separated over the base and `𝒴`
quasi-separated over the base is quasi-compact and quasi-separated.

Quasi-compactness is part (1); quasi-separatedness is Stacks 050N part (8), whose hypothesis on
the relative diagonal of the structure morphism of `𝒴` is the second conjunct of
quasi-separatedness of `𝒴` over the base. -/
@[stacks 075S "part (2)", sga "4 VI 1.14" "(i), stacks, X also qs"]
theorem isQuasiCompactMorphism_and_isQuasiSeparated (hqs : QuasiSeparatedSpace S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (h𝒴 : IsQuasiSeparatedOver.{u, w} B S hS 𝒴) :
    IsQuasiCompactMorphism.{u, w} B S hS f ∧
      AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f :=
  ⟨isQuasiCompactMorphism_of_isQuasiCompactStack B S hS hqs f h𝒳qc h𝒴,
    AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS f h𝒳qs h𝒴.2⟩

/-- **Stacks 075S, part (3).** A 2-fibre product `𝒳 ×_𝒴 𝒵` of algebraic stacks over a
quasi-separated base scheme, with `𝒳`, `𝒵` quasi-compact and quasi-separated over the base and
`𝒴` quasi-separated over the base, is quasi-compact and quasi-separated over the base.

The projection to `𝒵` is a base change of `f`, which is quasi-compact and quasi-separated by
part (2), hence is itself quasi-compact (Stacks 050V) and quasi-separated (Stacks 050F). A
quasi-compact 1-morphism into the quasi-compact `𝒵` has quasi-compact source, and Stacks 050L
part (4) carries quasi-separatedness over the base from `𝒵` to the apex. -/
@[stacks 075S "part (3)"]
theorem isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct
    (hqs : QuasiSeparatedSpace S) {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (h𝒵qc : IsQuasiCompactStack.{u, w} B S hS 𝒵.val 𝒵.property)
    (h𝒵qs : IsQuasiSeparatedOver.{u, w} B S hS 𝒵)
    (h𝒴 : IsQuasiSeparatedOver.{u, w} B S hS 𝒴) :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductAlgebraicStack B S hS f g).property ∧
      IsQuasiSeparatedOver.{u, w} B S hS (twoFibreProductAlgebraicStack B S hS f g) := by
  obtain ⟨hfqc, hfqs⟩ := isQuasiCompactMorphism_and_isQuasiSeparated B S hS hqs f h𝒳qc h𝒳qs h𝒴
  have hprojqc : IsQuasiCompactMorphism.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isQuasiCompactMorphism_baseChange B S hS f g
      (twoFibreProductSquareAlgebraicStacks B S hS f g).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)) hfqc
  have hprojqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    AlgebraicStacks.isQuasiSeparated_baseChange B S hS f g hfqs
  exact ⟨isQuasiCompactStack_of_isQuasiCompactMorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd hprojqc h𝒵qc,
    AlgebraicStacks.isQuasiSeparatedOver_of_isQuasiSeparated B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd h𝒵qs hprojqs⟩

end AlgebraicGeometry.Stack

end
