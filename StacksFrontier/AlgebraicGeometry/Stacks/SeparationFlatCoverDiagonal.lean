module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivityProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductProjectionCancellation

/-!
# The separation axioms read off a flat cover by an algebraic space (Stacks 06MB)

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, let `𝒲` be an
algebraic stack over `S` which is representable by an algebraic space, and let `f : 𝒲 ⟶ 𝒳` be
surjective, flat and locally of finite presentation. **Stacks 06MB** reads two separation
properties of `𝒳` off `f`: if `f` is unramified then `𝒳` is Deligne–Mumford, and if `f` is
locally quasi-finite then `𝒳` is quasi-DM.

Both conclusions are properties of the absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳`, and both are tested
along the cover `f × f : 𝒲 × 𝒲 ⟶ 𝒳 × 𝒳`, which is again locally essentially surjective. The base
change of `Δ` along it is the projection

```text
  𝒲 ×_𝒳 𝒲 ⟶ 𝒲 × 𝒲
```

of **Stacks 02XE**, and composing that projection with a projection of the product gives the
first projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲`, a base change of `f`. So a property of `f` which is stable under
base change (**Stacks 045C**) and inherited by the first factor of a composite transfers to the
represented base change of `Δ`, whence to `Δ` itself by **Stacks 04XD**. The cancellation step is
`AlgebraicGeometry.Stack.prop_representingMap_relativeDiagonalSquare_fst`, which for
unramifiedness is **Stacks 06G6** and for local quasi-finiteness **Stacks 03XN**.

Finally the separation axioms of **Stacks 050D** are stated for the relative diagonal of the
structure 1-morphism, and the absolute diagonal has the same relative properties as that one by
`AlgebraicGeometry.Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism`; the
absolute forms, parts (5) and (6) of Stacks 050D, are reached by **Stacks 050N**.

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_productMap_of_flatCover`: the self-product of the cover
  is locally essentially surjective.
* `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_flatCover`: a property of `f` stable
  under base change, local at the target and inherited by first factors is a property of the
  absolute diagonal of `𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover`:
  **Stacks 06MB**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover`:
  **Stacks 06MB**, part (2).

## Implementation notes

**Unramifiedness of `f` is the relative notion of Stacks 03YK**, written through
`AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.unramifiedMorphismProperty`, and *not*
`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**), which has the Deligne–Mumford condition
as a conjunct and would make part (1) circular. The two instance arguments of
`HasRelativeProperty` are base-change stability (**Stacks 03ZJ**) and target locality
(**Stacks 042A**, available for the fpqc precoverage and transported down to the fppf one), and
neither is an instance at unramifiedness in this library; so both are introduced by `haveI`
inside the hypothesis' type, exactly as in
`AlgebraicGeometry.Stack.isUnramified_representingMap_relativeDiagonalSquare_fst`. Local
quasi-finiteness needs only the first, the second being found by instance search.

The three hypotheses on the cover are the library's named notions, as in **Stacks 06TZ**:
surjectivity on points (Stacks 04ZS), the existential smooth-diagram condition of Stacks 06PW and
the universal one of Stacks 06Q2 part (1). They are converted into the relative properties of
Stacks 03YK by **Stacks 04XI** and twice by **Stacks 06FM**, the local finite presentation case
passing first through
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`; this is the conversion
`AlgebraicGeometry.Stack.localEssSurj_diagonalMapDiag` performs as well.

**Stacks 04XD is used through its local essential surjectivity form.** The hypothesis
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj` makes on
the cover is weaker than the one of `…_of_fppf`, and it is the one available here: the conjunction
of surjectivity, flatness and local finite presentation carries neither
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` nor
`CategoryTheory.MorphismProperty.IsLocalAtTarget` nor
`CategoryTheory.MorphismProperty.IsStableUnderComposition`, so Stacks 045E is unavailable for
`f × f`, while `AlgebraicGeometry.Stack.localEssSurj_productMap` needs nothing of the property.

The two representing algebraic spaces that Stacks 04XD and the cancellation step consume are
extracted inside the proof: `𝒲 × 𝒲` is represented by an algebraic space because `𝒲` is, and
`𝒲 ×_𝒳 𝒲` is by **Stacks 0300**, `f` being representable by algebraic spaces.

The parenthetical of part (1) — that an unramified `f` is étale here — is not delivered. Its
content at the level of morphisms of algebraic spaces is
`AlgebraicGeometry.Space.isEtale_of_isFlat_of_isUnramified` (**Stacks 06LU**), and lifting it to
the relative notion of Stacks 03YK is independent of the two statements below.

Every universe is pinned by hand at `u`, as in Stacks 06TZ: the index universe of the fppf
precoverage occurs only in the `CategoryTheory.MorphismProperty.IsLocalAtTarget` instance binder
of `AlgebraicGeometry.Stack.HasRelativeProperty` and so is not determined by the explicit
arguments.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The self-product of a surjective, flat and locally finitely presented cover by an algebraic
space is locally essentially surjective.** For `f : 𝒲 ⟶ 𝒳` a 1-morphism of algebraic stacks over
`S` with `𝒲` representable by an algebraic space, every object of a fibre of `𝒳 × 𝒳` becomes,
after restriction to a covering sieve of the big fppf topology, isomorphic to the image of an
object of `𝒲 × 𝒲` under `f × f`. -/
theorem localEssSurj_productMap_of_flatCover
    {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val)
    (hSurj : IsSurjective B S hS f)
    (hFlat : AlgebraicStacks.IsFlat B S hS f)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∀ (U : BigFppfOver B S hS)
      (t : (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (CatFiberedInGroupoids.product 𝒲.val 𝒲.val).val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor
                (CatFiberedInGroupoids.productMap f.hom f.hom)).obj z ⟶ t.1,
              (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p.IsHomLift k φ := by
  have hfr : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom
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
  have hle := localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS f.hom hfr
    (fun U y hy F hF he =>
      ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hfr).1
          hSurj U y hy F hF he,
        (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒲.property 𝒳.property
          f.hom hfr).1 hFlat U y hy F hF he,
        (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
          𝒲.property 𝒳.property f.hom hfr).1
            ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
              (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
              𝒲.property 𝒳.property f.hom).1 hLfp) U y hy F hF he⟩)
  exact localEssSurj_productMap B S hS f.hom f.hom hle hle

/-- **A relative property of a flat cover by an algebraic space is a relative property of the
absolute diagonal.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change, local at the target for the fppf precoverage and inherited by the first
factor of a composite that has it, and let `f : 𝒲 ⟶ 𝒳` be surjective, flat and locally of finite
presentation with `𝒲` representable by an algebraic space. If `f` has the relative property `P`
of Stacks 03YK, then so does the absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳`.

The base change of `Δ` along `f × f` is the projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲 × 𝒲` of Stacks 02XE, which
has `P` on representing algebraic spaces by cancelling a product projection off the base change
`𝒲 ×_𝒳 𝒲 ⟶ 𝒲` of `f`; Stacks 04XD then carries `P` to `Δ`. -/
theorem hasRelativeProperty_diagonal_of_flatCover
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val)
    (hSurj : IsSurjective B S hS f)
    (hFlat : AlgebraicStacks.IsFlat B S hS f)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hcancel : ∀ ⦃X Y Z : AlgebraicSpaces B S hS⦄ (a : X ⟶ Y) (b : Y ⟶ Z), P (a ≫ b) → P a)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P f.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P (diagonal.{u, u, u + 1} B S hS 𝒳.val)
      (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳) := by
  have hfr : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_product B S hS 𝒲.val 𝒲.val h𝒲 h𝒲
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    𝒳.val 𝒲.val 𝒲.val f.hom.hom f.hom.hom hfr h𝒲
  exact hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS P 𝒳.val
    (CatFiberedInGroupoids.product 𝒳.val 𝒳.val) (CatFiberedInGroupoids.product 𝒲.val 𝒲.val)
    (diagonal.{u, u, u + 1} B S hS 𝒳.val) (CatFiberedInGroupoids.productMap f.hom f.hom)
    (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳)
    (localEssSurj_productMap_of_flatCover B S hS f h𝒲 hSurj hFlat hLfp)
    (relativeDiagonalSquare.{u, u, u} B S hS 𝒲.val 𝒲.val 𝒳.val f.hom f.hom)
    (isTwoFibreProduct_relativeDiagonalSquare.{u, u, u} B S hS 𝒲.val 𝒲.val 𝒳.val f.hom f.hom)
    V W hV hW eV eW
    (prop_representingMap_relativeDiagonalSquare_fst B S hS P 𝒲.val 𝒳.val f.hom hfr h𝒲
      V W hV hW eV eW hcancel
      (relativeProperty_baseChange.{u, u, u + 1} B S hS P 𝒲.val 𝒳.val 𝒲.val f.hom f.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom f.hom) hP))

namespace AlgebraicStacks

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 06MB, part (1).** Let `𝒳` be an algebraic stack over `S` and let `f : 𝒲 ⟶ 𝒳` be
surjective, flat and locally of finite presentation with `𝒲` representable by an algebraic space.
If `f` is unramified in the relative sense of Stacks 03YK, then `𝒳` is Deligne–Mumford.

Unramifiedness passes from `f` to the absolute diagonal of `𝒳` by
`AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_flatCover`, the cancellation of first
factors being Stacks 06G6; the absolute diagonal and the relative diagonal of the structure
1-morphism have the same relative properties, and Stacks 050N part (1) turns DM over `S` into
DM. -/
@[stacks 06MB "part (1)"]
theorem isAbsolutelyDM_of_isUnramified_flatCover
    {𝒳 𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val)
    (hSurj : IsSurjective B S hS f)
    (hFlat : IsFlat B S hS f)
    (hLfp : IsLocallyOfFinitePresentation B S hS f)
    (hUnr : haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
        Space.isUnramified_isStableUnderBaseChange B S hS
      haveI : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
        (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
          (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
        f.hom
        (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom)) :
    IsAbsolutelyDM.{u, w} B S hS hZ 𝒳 := by
  have hBC : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have hLT : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact isAbsolutelyDM_of_isDMOver.{u, w} B S hS hZ 𝒳
    ⟨Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
        (Stack.structureMorphism.{u, w} B S hS 𝒳),
      (Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
          (Space.unramifiedMorphismProperty B S hS)).mp
        (Stack.hasRelativeProperty_diagonal_of_flatCover B S hS
          (Space.unramifiedMorphismProperty B S hS) f h𝒲 hSurj hFlat hLfp
          (fun {X Y Z} a b h => Space.isUnramified_of_comp B S hS X.property Y.property
            Z.property a.hom b.hom h) hUnr)⟩

/-- **Stacks 06MB, part (2).** Let `𝒳` be an algebraic stack over `S` and let `f : 𝒲 ⟶ 𝒳` be
surjective, flat and locally of finite presentation with `𝒲` representable by an algebraic space.
If `f` is locally quasi-finite in the relative sense of Stacks 03YK, then `𝒳` is quasi-DM.

This is the argument of part (1) with the cancellation of first factors supplied by
Stacks 03XN. -/
@[stacks 06MB "part (2)"]
theorem isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover
    {𝒳 𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val)
    (hSurj : IsSurjective B S hS f)
    (hFlat : IsFlat B S hS f)
    (hLfp : IsLocallyOfFinitePresentation B S hS f)
    (hQf : haveI : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
        Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.locallyQuasiFiniteProperty B S hS) f.hom
        (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom)) :
    IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 := by
  have hBC : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
    Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
  exact isAbsolutelyQuasiDM_of_isQuasiDMOver.{u, w} B S hS hZ 𝒳
    ((Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
        (Space.locallyQuasiFiniteProperty B S hS)).mp
      (Stack.hasRelativeProperty_diagonal_of_flatCover B S hS
        (Space.locallyQuasiFiniteProperty B S hS) f h𝒲 hSurj hFlat hLfp
        (fun {X Y Z} a b h => Space.isLocallyQuasiFinite_of_comp B S hS X.property Y.property
          Z.property a.hom b.hom h) hQf))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
