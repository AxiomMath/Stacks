module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCoverBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# The separation axioms descend along an fppf cover by an algebraic space (Stacks 06TZ)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `g : 𝒴' ⟶ 𝒴` be a
1-morphism which is surjective, flat and locally of finite presentation and whose source is
representable by an algebraic space. **Stacks 06TZ** says that each of the separation conditions
of Stacks 04YW holds for `f` as soon as it holds for the base change
`f' : 𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'`.

The proof is the mirror of Stacks 050F
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_baseChange` and its siblings) with the
implication turned round. By Stacks 04YR the square

```text
            Δ_{f'}
    𝒰  ------------->  𝒰 ×_{𝒴'} 𝒰
    |                       |
  r |                       | r × r
    v                       v
    𝒳  --Δ_f-------->  𝒳 ×_𝒴 𝒳
```

is 2-cartesian (`AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare`), so `Δ_{f'}`
is a base change of `Δ_f` along `r × r`; and each of the conditions of Stacks 04YW is a property
of the relative diagonal in the relative sense of Stacks 03YK. Where Stacks 050F transports such
a property *forward* along the base change by Stacks 045C, this module descends it *backward* by
**Stacks 045D**, whose hypothesis is the local essential surjectivity of `r × r`.

That hypothesis is the content of the module, and it is where the cover being an algebraic space
is used. Its three steps are:

* `g` is representable by algebraic spaces, because its source is representable by an algebraic
  space and its target is an algebraic stack;
* `r` is a base change of `g` and `r × r` is a base change of `r` — the latter by the square
  `AlgebraicGeometry.Stack.diagonalCoverSquare` — so both are representable by algebraic spaces
  by Stacks 0302, and both are surjective, flat and locally of finite presentation in the
  relative sense of Stacks 03YK by Stacks 045C;
* a 1-morphism representable by algebraic spaces with those three relative properties is locally
  essentially surjective
  (`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`).

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_diagonalMapDiag`: local essential surjectivity of
  `r × r`, the hypothesis Stacks 045D consumes.
* `AlgebraicGeometry.Stack.isDM_of_isDM_baseChange`: **Stacks 06TZ**, the Deligne–Mumford case.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isQuasiDM_baseChange`: **Stacks 06TZ**,
  the quasi-DM case.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isSeparated_baseChange`:
  **Stacks 06TZ**, the separated case.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparated_baseChange`:
  **Stacks 06TZ**, the quasi-separated case.

## Implementation notes

**The hypotheses on `g` are the library's named notions, not the longhand quantifier.**
Surjectivity is Stacks 04ZS — surjectivity on points — flatness is the existential
smooth-diagram condition of Stacks 06PW and local finite presentation is the universal one of
Stacks 06Q2 part (1). The three are converted into the relative properties of Stacks 03YK that
Stacks 045C transports, by
`AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective` (**Stacks 04XI**) and
twice by
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_relative`
(**Stacks 06FM** for a representable morphism), the local finite presentation case passing first
through `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` because of the
asymmetry between Stacks 06PW and Stacks 06Q2 — the same asymmetry
`StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients` records.

Three of those four conversions name a universe explicitly. Stacks 04XI and Stacks 06FM are
stated through the abbreviation `AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK,
whose `[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]` instance binder is the only
place the index universe of the precoverage occurs; so that universe is not determined by the
arguments and has to be pinned at the call site, here at `u`, which is the weakest member of the
family of locality hypotheses and therefore the strongest statement available. The same binder is
why `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` is applied with its universes
written out as `.{u, u, u, u}`.

**Stacks 045C is used in the longhand form, which carries no hypothesis on the property.**
`AlgebraicGeometry.Stack.relativeProperty_baseChange` is Stacks 045C with its two
instance arguments dropped, and the three relative properties of `g` are transported as a single
`CategoryTheory.MorphismProperty` — their conjunction — in one application per square. Neither
that conjunction nor its first component carries the instances: the conjunction has them for
neither `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` nor
`CategoryTheory.MorphismProperty.IsLocalAtTarget` (`.inf` does not fire, surjectivity's
instances being registered at `AlgebraicGeometry.Space.surjectiveMorphismProperty` and flatness's
target locality being a theorem rather than an instance), so the longhand form of Stacks 045C is
not a convenience here but the only form that applies.

**Stacks 045D, by contrast, genuinely needs both instances**, being a descent statement: its
proof extracts a covering family from a covering sieve and glues. They are available for all
four properties below, and each case names the pair it uses. The quasi-DM case finds the target
locality by instance search and supplies
`AlgebraicGeometry.Space.isLocallyQuasiFinite_isStableUnderBaseChange`, which is a theorem and not
an instance; the Deligne–Mumford case supplies
`AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange` and transports
`AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` down to the fppf precoverage; the
quasi-separated case forms both as meets of the quasi-compact and quasi-separated instances; the
separated case supplies `AlgebraicGeometry.Space.isProper_isStableUnderBaseChange`
(**Stacks 04WP**) and `AlgebraicGeometry.Space.proper_isLocalAtTarget_fppf`, the fppf form of
**Stacks 0422**, which is properness read as the meet of separatedness, finite type and universal
closedness, each of the three being fpqc local on the base by Stacks 0421, 041U and 041O.

**On the import surface.** `StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective` (Stacks 04XI,
`AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective`) and
`StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces`
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`) are imported
directly, both being needed by the local essential surjectivity lemma below. Neither is
transitively exported along any other import of this module, so neither may be dropped on the
grounds that its module is reachable: in the module system reachability of a module is not
visibility of its declarations.
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite` is likewise required: it is the only
provider of `AlgebraicGeometry.Space.isLocallyQuasiFinite_isStableUnderBaseChange`, which the
quasi-DM case below needs and cannot obtain by instance search.
`StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget` carries both inputs of the
separated case: `AlgebraicGeometry.Space.proper_isLocalAtTarget_fppf` is declared there, and
`AlgebraicGeometry.Space.isProper_isStableUnderBaseChange` is re-exported along its imports, so
`StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange` need not be named as well.
`StacksCore.Tactic.StacksAttribute` is also removable and is **retained as cosmetic**, because it
provides the attribute the four results actually carry.

**The base change is the canonical one.** As in Stacks 050F, the statements are not
quantified over an arbitrary 2-fibre product square of the cospan `(g, f)`: the square of
Stacks 04YR is formalized over the canonical apex only, so an arbitrary apex would need a comparison
of `𝒰 ×_{𝒴'} 𝒰` with `W ×_{𝒴'} W`. The source states Stacks 06TZ for *the* base change
`𝒲 ×_𝒴 𝒳 ⟶ 𝒲`, which is `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`' second
projection, so nothing of the source's statement is lost.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 041O](https://stacks.math.columbia.edu/tag/041O)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **The self-product of an fppf cover by an algebraic space is locally essentially
surjective.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` with
`𝒴'` representable by an algebraic space and `g` surjective, flat and locally of finite
presentation, and write `𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'` and `r : 𝒰 ⟶ 𝒳` for its first projection. Then
every object of a fibre of `𝒳 ×_𝒴 𝒳` becomes, after restriction to a covering sieve of the big
fppf topology, isomorphic to the image of an object of `𝒰 ×_{𝒴'} 𝒰` under `r × r`.

This is the hypothesis `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`
(**Stacks 045D**) consumes. -/
theorem localEssSurj_diagonalMapDiag (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g) :
    ∀ (U : BigFppfOver B S hS)
      (y : (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (twoFibreProduct B S hS 𝒴'.val
              (twoFibreProductAlgebraicStack B S hS f g).val
              (twoFibreProductAlgebraicStack B S hS f g).val
              (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
              (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom).val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor (diagonalMapDiag B S hS f g)).obj z ⟶ y.1,
              (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val
                f.hom.hom f.hom.hom).val.p.IsHomLift k φ := by
  -- `g` is representable by algebraic spaces, its source being an algebraic space.
  have hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property h𝒴' g.hom
  -- `r` is a base change of `g`, so Stacks 0302 makes it representable by algebraic spaces.
  have hr : IsRepresentableByAlgebraicSpaces B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒴'.val 𝒴.val 𝒳.val
      g.hom f.hom (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom g.hom) hgr
  -- `r × r` is a base change of `r` along `pr₁`, by `diagonalCoverSquare`; Stacks 0302 again.
  have hrr : IsRepresentableByAlgebraicSpaces B S hS (diagonalMapDiag B S hS f g).hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (twoFibreProductAlgebraicStack B S hS f g).val 𝒳.val
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom)
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom (diagonalProdFst B S hS f)
      (diagonalCoverSquare B S hS f g) (isTwoFibreProduct_diagonalCoverSquare B S hS f g) hr
  refine localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS
    (diagonalMapDiag B S hS f g) hrr ?_
  -- the three relative properties travel from `r` to `r × r` along `diagonalCoverSquare` ...
  refine relativeProperty_baseChange.{u, u, u + 1} B S hS
    (fun _ _ k => Space.IsSurjective B S hS k.hom ∧ Space.IsFlat B S hS k.hom ∧
      Space.IsLocallyOfFinitePresentation B S hS k.hom)
    (twoFibreProductAlgebraicStack B S hS f g).val 𝒳.val
    (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom)
    (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom (diagonalProdFst B S hS f)
    (diagonalCoverSquare B S hS f g) (isTwoFibreProduct_diagonalCoverSquare B S hS f g) ?_
  -- ... and from `g` to `r` along the canonical square of the cospan `(f, g)`.
  refine relativeProperty_baseChange.{u, u, u + 1} B S hS
    (fun _ _ k => Space.IsSurjective B S hS k.hom ∧ Space.IsFlat B S hS k.hom ∧
      Space.IsLocallyOfFinitePresentation B S hS k.hom)
    𝒴'.val 𝒴.val 𝒳.val g.hom f.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom g.hom) ?_
  -- what remains is the conversion of the three named notions into relative properties.
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  intro U y hy F hF he
  exact ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hgr).1
      hgSurj U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒴'.property 𝒴.property
      g.hom hgr).1 hgFlat U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒴'.property 𝒴.property g.hom hgr).1
        ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
          𝒴'.property 𝒴.property g.hom).1 hgLfp) U y hy F hF he⟩

/-- Descent of a relative property of the relative diagonal `Δ_f` along `r × r`, given that the
base change `Δ_{f'}` has it (Stacks 045D with the hypothesis `localEssSurj_diagonalMapDiag`). -/
private theorem hasRelativeProperty_relativeDiagonal_of_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hP : HasRelativeProperty B S hS P (diagonalBaseChangeSquare B S hS f g).fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
        (diagonalMapDiag B S hS f g) (diagonalBaseChangeSquare B S hS f g)
        (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f g)
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f))) :
    HasRelativeProperty B S hS P (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f) :=
  hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS 𝒳.val
    (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _ P
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
    (diagonalMapDiag B S hS f g) (diagonalBaseChangeSquare B S hS f g)
    (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f g)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (localEssSurj_diagonalMapDiag B S hS f g h𝒴' hgSurj hgFlat hgLfp) hP

/-- **Stacks 06TZ, the Deligne–Mumford case.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` and let `g : 𝒴' ⟶ 𝒴` be surjective, flat and locally of finite presentation with
`𝒴'` representable by an algebraic space. If the base change
`f' : 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'` of `f` by `g` is Deligne–Mumford, so is `f`.

By Stacks 04YR the relative diagonal `Δ_{f'}` is a base change of `Δ_f` along `r × r`, and
unramifiedness in the relative sense of Stacks 03YK descends along `r × r` by Stacks 045D, whose
local essential surjectivity hypothesis is
`AlgebraicGeometry.Stack.localEssSurj_diagonalMapDiag`. The representability witness is
Stacks 04XS part (1), which holds for every 1-morphism of algebraic stacks and so is not
descended. -/
@[stacks 06TZ "dm_descent"]
theorem isDM_of_isDM_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hf' : IsDM B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsDM B S hS f := by
  obtain ⟨-, hP'⟩ := hf'
  have hunrBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsUnramified B S hS h)).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have hunrLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsUnramified B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  exact hasRelativeProperty_relativeDiagonal_of_baseChange B S hS
    (fun _ _ k => Space.IsUnramified B S hS k.hom) f g h𝒴' hgSurj hgFlat hgLfp hP'

namespace AlgebraicStacks

/-- **Stacks 06TZ, the quasi-DM case.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S` and let `g : 𝒴' ⟶ 𝒴` be surjective, flat and locally of finite presentation with `𝒴'`
representable by an algebraic space. If the base change `f' : 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'` of `f` by
`g` is quasi-DM, so is `f`.

The relative diagonal of the base change is a base change of `Δ_f` by Stacks 04YR, and local
quasi-finiteness of the represented base changes descends by Stacks 045D. -/
@[stacks 06TZ "quasi_dm_descent"]
theorem isQuasiDM_of_isQuasiDM_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hf' : IsQuasiDM B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsQuasiDM B S hS f := by
  have hlqfBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyQuasiFinite B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
  exact hasRelativeProperty_relativeDiagonal_of_baseChange B S hS
    (fun _ _ k => Space.IsLocallyQuasiFinite B S hS k.hom) f g h𝒴' hgSurj hgFlat hgLfp hf'

/-- **Stacks 06TZ, the separated case.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S` and let `g : 𝒴' ⟶ 𝒴` be surjective, flat and locally of finite presentation with `𝒴'`
representable by an algebraic space. If the base change `f' : 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'` of `f` by
`g` is separated, so is `f`.

The relative diagonal of the base change is a base change of `Δ_f` by Stacks 04YR, and properness
of the represented base changes descends by Stacks 045D, whose target-locality hypothesis is the
fppf form of Stacks 0422. -/
@[stacks 06TZ "separated_descent"]
theorem isSeparated_of_isSeparated_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hf' : IsSeparated B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsSeparated B S hS f := by
  have hprBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hprLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  exact hasRelativeProperty_relativeDiagonal_of_baseChange B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom) f g h𝒴' hgSurj hgFlat hgLfp hf'

/-- **Stacks 06TZ, the quasi-separated case.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` and let `g : 𝒴' ⟶ 𝒴` be surjective, flat and locally of finite presentation with
`𝒴'` representable by an algebraic space. If the base change `f' : 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'` of `f`
by `g` is quasi-separated, so is `f`.

The relative diagonal of the base change is a base change of `Δ_f` by Stacks 04YR, and the
conjunction of quasi-compactness and quasi-separatedness of the represented base changes descends
by Stacks 045D — applied at the *conjunction*, read as a property of morphisms of algebraic
spaces, exactly as the definition of quasi-separatedness is, with both of that conjunction's
hypotheses formed as meets. -/
@[stacks 06TZ "quasi_separated_descent"]
theorem isQuasiSeparated_of_isQuasiSeparated_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (h𝒴' : IsRepresentableByAlgebraicSpace B S hS 𝒴'.val)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hf' : IsQuasiSeparated B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsQuasiSeparated B S hS f := by
  have hqsBC : (spaceProperty B S hS (fun _ _ h =>
      Space.IsQuasiCompact B S hS h ∧
        Space.IsQuasiSeparated B S hS h)).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have hqsLT : (spaceProperty B S hS (fun _ _ h =>
      Space.IsQuasiCompact B S hS h ∧
        Space.IsQuasiSeparated B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  exact (isQuasiSeparated_iff_forall B S hS f).2
    (hasRelativeProperty_relativeDiagonal_of_baseChange B S hS
      (fun _ _ k => Space.IsQuasiCompact B S hS k.hom ∧ Space.IsQuasiSeparated B S hS k.hom)
      f g h𝒴' hgSurj hgFlat hgLfp
      ((isQuasiSeparated_iff_forall B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd).1 hf'))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
