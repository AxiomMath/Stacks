module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange

/-!
# A reduced quasi-separated algebraic stack with irreducible space is integral (Stacks 0GWD)

An algebraic stack `𝒳` over a scheme `S` contained in a big fppf site `B` is *integral*
(**Stacks 0GWB**) when four conditions hold: it is reduced, it is decent, its inertia projection
`I_𝒳 ⟶ 𝒳` is quasi-compact, and its space of points `|𝒳|` is irreducible. **Stacks 0GWD** says
that for a quasi-separated algebraic stack the first and the last of those already imply the
other two, so that a reduced quasi-separated algebraic stack with irreducible space of points is
integral.

The two conditions to be produced are the source's:

* decency is **Stacks 0GW2**, the quasi-separated case, which is proved as
  `AlgebraicGeometry.Stack.isDecent_of_isQuasiSeparated`;
* quasi-compactness of `I_𝒳 ⟶ 𝒳` is **Stacks 050V** — base change preserves quasi-compactness —
  applied to the absolute diagonal, because the inertia is the 2-fibre product
  `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` of **Stacks 034H** (1) and the inertia projection is the base change of
  `Δ` along `Δ`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompact_diagonal_of_isAbsolutelyQuasiSeparated`: the absolute
  diagonal of a quasi-separated algebraic stack is quasi-compact in the sense of Properties of
  Stacks, Section 04XB.
* `AlgebraicGeometry.Stack.isQuasiCompact_inertiaProjection`: the Section 04XB form of
  quasi-compactness of the inertia projection, from quasi-compactness of the absolute diagonal.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks`: the same in
  the sense of **Stacks 050U**, which is the form the third conjunct of Stacks 0GWB is stated in.
* `AlgebraicGeometry.Stack.isIntegral_of_isReducedStack_of_isAbsolutelyQuasiSeparated`:
  **Stacks 0GWD**.
* `AlgebraicGeometry.Stack.isIntegral_of_isReducedStack_of_isQuasiCompact_diagonal`: the
  strengthening the source records parenthetically at the end of the proof of Stacks 0GWD —
  "quasi-separated" may be replaced by "`Δ_𝒳` is quasi-compact".

## Implementation notes

The base change of `Δ` along `Δ` is run at the relative property of Properties of Stacks,
Section 04XB rather than at the Stacks 050U condition on 1-morphisms of algebraic stacks, and the
two are reconciled once, at the end, by Stacks 050T
(`AlgebraicGeometry.Stack.isQuasiCompact_iff_baseChange_quasiCompact`); the representability by
algebraic spaces that Stacks 050T asks of the inertia projection is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack`,
so it never has to be assumed. Working at Section 04XB is what makes the identification of the
inertia with the second 2-fibre product of the diagonal usable: that identification is an
equivalence **over the site**, not an isomorphism of 1-morphisms of algebraic stacks, and the
Section 04XB quantifier transports along such an equivalence of sources with no hypothesis on the
property at all (`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, Stacks 0457), while
the Stacks 050U condition would require the comparison 1-morphism itself to be recognised as a
base change.

So the proof of quasi-compactness of the inertia projection is the proof of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection` with the property
changed: the canonical 2-fibre product square of the cospan `(Δ, Δ)`, then Stacks 045C
(`AlgebraicGeometry.Stack.relativeProperty_baseChange`) in place of Stacks 0302, then the
transport along `CategoryTheory.TwoFibreProductOver.ofRelativeInertia` in place of the
representability transport. The 2-commutativity datum of that transport is `Iso.refl`, because
the comparison followed by the first projection *is* the inertia projection on the nose.

The absolute diagonal is reached from quasi-separatedness in three existing steps and no new
mathematics: Stacks 050D part (8) implying part (4)
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`),
then part (2) of Stacks 04Z0
(`AlgebraicGeometry.Stack.isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals`) whose first
conjunct is quasi-compactness of the relative diagonal of the structure morphism, then
`AlgebraicGeometry.Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism`, which
identifies the Section 04XB conditions of that relative diagonal and of the absolute diagonal.
The last step is needed because the target of the absolute diagonal is the 2-fibre product over
the final object of the 2-category, while the target of the relative diagonal of the structure
morphism is the 2-fibre product over the algebraic stack represented by `S`; the two base objects
are equivalent but not equal.

Only `AlgebraicGeometry.Stack.isIntegral_of_isReducedStack_of_isAbsolutelyQuasiSeparated` carries
the tag of this section. The three lemmas before it are steps, and
`AlgebraicGeometry.Stack.isIntegral_of_isReducedStack_of_isQuasiCompact_diagonal` is the remark
the source makes inside the proof of Stacks 0GWD rather than the lemma Stacks 0GWD states, so it
carries no key: its decency input is the other assertion of Stacks 0GW2, whose key is registered
where that assertion is proved.

## References

* [Stacks Project, Tag 0GWD](https://stacks.math.columbia.edu/tag/0GWD)
* [Stacks Project, Tag 0GWB](https://stacks.math.columbia.edu/tag/0GWB)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The absolute diagonal of a quasi-separated algebraic stack is quasi-compact**, in the sense
of Properties of Stacks, Section 04XB.

Absolute quasi-separatedness is quasi-separatedness of the structure morphism of Stacks 050D,
whose first and second relative diagonals are then quasi-compact by part (2) of Stacks 04Z0; and
the absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfies the conditions of Section 04XB for exactly the
same properties as the relative diagonal of the structure morphism, the targets of the two
differing by the equivalence between the final object of the 2-category and the algebraic stack
represented by `S`. -/
theorem isQuasiCompact_diagonal_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    IsQuasiCompact B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val) :=
  (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
      (Space.quasiCompactProperty B S hS)).2
    ((isQuasiCompactMorphism_relativeDiagonal_iff B S hS
        (structureMorphism.{u, w} B S hS 𝒳)).1
      ((isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals B S hS
          (structureMorphism.{u, w} B S hS 𝒳)).1
        (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒳 h𝒳)).1)

/-- **The inertia projection of an algebraic stack with quasi-compact absolute diagonal is
quasi-compact**, in the sense of Properties of Stacks, Section 04XB.

By Stacks 034H (1) the inertia is the 2-fibre product `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`, and under that
identification the forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` is the first projection of the canonical
2-fibre product square over the cospan `(Δ, Δ)`, hence a base change of `Δ`; so this is
Stacks 045C transported along that equivalence of sources by Stacks 0457. -/
theorem isQuasiCompact_inertiaProjection (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompact B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val)) :
    IsQuasiCompact B S hS (inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳).hom := by
  have hG : 𝒳.val.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.val.p := Functor.comp_id _
  set P := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (diagonal.{u, u, u + 1} B S hS 𝒳.val) (diagonal.{u, u, u + 1} B S hS 𝒳.val)
  have h1 : IsQuasiCompact B S hS P.fst :=
    relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.quasiCompactProperty B S hS)
      𝒳.val (CatFiberedInGroupoids.product 𝒳.val 𝒳.val) 𝒳.val
      (diagonal.{u, u, u + 1} B S hS 𝒳.val) (diagonal.{u, u, u + 1} B S hS 𝒳.val) P
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _) hΔ
  let aFun : (inertia B S hS 𝒳.val).val ⥤ᵇ P.pt.val :=
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
  have hequiv : Functor.IsEquivalence aFun.toFunctor :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
      (TwoFibreProductOver.toRelativeInertia hG)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
      (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact relativeProperty_of_equivalences B S hS (Space.quasiCompactProperty B S hS)
    (inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳).hom.hom P.fst.hom aFun
    (BasedFunctor.id 𝒳.val.val) (Iso.refl _) h1

/-- **The inertia projection of an algebraic stack with quasi-compact absolute diagonal is
quasi-compact**, in the sense of Stacks 050U: every base change of it by a quasi-compact
algebraic stack is a quasi-compact algebraic stack. This is the form the third conjunct of
Stacks 0GWB is stated in.

`AlgebraicGeometry.Stack.isQuasiCompact_inertiaProjection` read through Stacks 050T, whose
representability hypothesis for the inertia projection is Stacks 050Q. -/
theorem isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompact B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val)) :
    IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳) :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS
      (inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳)
      (isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
        B S hS 𝒳.val 𝒳.property)).1
    (isQuasiCompact_inertiaProjection.{u, w} B S hS 𝒳 hΔ)

/-- **Stacks 0GWD.** An algebraic stack `𝒳` over `S` which is reduced and quasi-separated and
whose space of points `|𝒳|` is irreducible is integral in the sense of Stacks 0GWB.

Two of the four conditions of Stacks 0GWB are hypotheses. Decency is Stacks 0GW2 for a
quasi-separated algebraic stack. Quasi-compactness of the inertia projection `I_𝒳 ⟶ 𝒳` holds
because that 1-morphism is the base change of the absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` along
itself, and `Δ` is quasi-compact since `𝒳` is quasi-separated. -/
@[stacks 0GWD]
theorem isIntegral_of_isReducedStack_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hred : IsReducedStack.{u, w} B S hS 𝒳)
    (hqs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (hirr : @IrreducibleSpace (points B S hS 𝒳.val.val 𝒳.val.property)
      (pointTopology B S hS 𝒳.val)) :
    IsIntegral.{u, w} B S hS 𝒳 :=
  ⟨hred, isDecent_of_isQuasiSeparated B S hS hZ 𝒳 hqs,
    isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳
      (isQuasiCompact_diagonal_of_isAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳 hqs),
    hirr⟩

/-- **The strengthening of Stacks 0GWD recorded at the end of its proof:** in the statement of
Stacks 0GWD, "quasi-separated" may be replaced by "the absolute diagonal `Δ_𝒳` is quasi-compact".

Quasi-separatedness is used twice in Stacks 0GWD and each use needs only quasi-compactness of the
absolute diagonal: decency is the other assertion of Stacks 0GW2
(`AlgebraicGeometry.Stack.isDecent_of_isQuasiCompact_diagonal`), and quasi-compactness of the
inertia projection was already derived from quasi-compactness of `Δ_𝒳` alone. The hypothesis is
read as in Stacks 050D, on the relative diagonal of the structure morphism of `𝒳` viewed over the
terminal scheme. -/
theorem isIntegral_of_isReducedStack_of_isQuasiCompact_diagonal
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hred : IsReducedStack.{u, w} B S hS 𝒳)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) hZ
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) hZ
        (structureMorphism B (⊤_ Scheme.{u}) hZ
          (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳))))
    (hirr : @IrreducibleSpace (points B S hS 𝒳.val.val 𝒳.val.property)
      (pointTopology B S hS 𝒳.val)) :
    IsIntegral.{u, w} B S hS 𝒳 :=
  ⟨hred, isDecent_of_isQuasiCompact_diagonal B S hS hZ 𝒳 hΔ,
    isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳
      ((relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
          (Space.quasiCompactProperty B S hS)).2
        (isQuasiCompact_relativeDiagonal_structureMorphism_of_absolute B S hS hZ 𝒳
          ((isQuasiCompactMorphism_relativeDiagonal_iff B (⊤_ Scheme.{u}) hZ
            (structureMorphism B (⊤_ Scheme.{u}) hZ
              (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳))).1 hΔ))),
    hirr⟩

end AlgebraicGeometry.Stack

end
