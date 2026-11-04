module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallySeparatedFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism

/-!
# Local separatedness of the relative inertia

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. We prove that the relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is
locally separated exactly when the first relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is, both
in the relative sense of Properties of Stacks, Section 04XB. This is the equivalence of
conditions (a) and (b) of part (3) of Stacks 0CL0. We also show that a section of a locally
separated 1-morphism representable by algebraic spaces is an immersion.

## Main results

* `AlgebraicGeometry.Stack.isLocallySeparated_relativeInertiaProjection_iff_relativeDiagonal`:
  the relative inertia projection of a 1-morphism of algebraic stacks is locally separated exactly
  when its first relative diagonal is.
* `AlgebraicGeometry.Stack.isImmersion_section_of_isLocallySeparated`: a section of a locally
  separated 1-morphism representable by algebraic spaces is an immersion.
* `AlgebraicGeometry.Stack.isImmersion_comparison_of_isImmersion_relativeDiagonal`,
  `AlgebraicGeometry.Stack.isImmersion_graph_of_isImmersion_relativeDiagonal`,
  `AlgebraicGeometry.Stack.isImmersion_section_of_isImmersion_relativeDiagonal`: the comparison
  1-morphism of Stacks 050H, a graph and a section are immersions as soon as the corresponding
  relative diagonal is.
* `AlgebraicGeometry.Stack.isLocallySeparated_relativeInertiaProjection_iff_twoFibreProductFst`:
  the relative inertia projection is locally separated exactly when the first projection of the
  2-fibre product of `Δ_f` with itself is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal`:
  that first projection is representable by algebraic spaces.

## References

* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A section of a locally separated 1-morphism is an immersion -/

section Section

variable {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- The comparison 1-morphism `𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of Stacks 050H is an immersion as soon as
the relative diagonal of `h : 𝒵 ⟶ 𝒯` is. -/
theorem isImmersion_comparison_of_isImmersion_relativeDiagonal
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)) :
    IsImmersion B S hS (comparison B S hS f g h).hom :=
  fun U y hy F hF he =>
    relativeProperty_baseChange.{u, u, u + 1} B S hS
      (fun _ _ k => Space.IsImmersion B S hS k.hom)
      𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
      (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
      (relativeDiagonalAlgebraicStacks B S hS h).hom
      (comparisonCospanRight B S hS f g h).hom
      (comparisonSquare B S hS f g h)
      (isTwoFibreProduct_comparisonSquare B S hS f g h) hh U y hy F hF he

/-- The graph of `g : 𝒳 ⟶ 𝒴` over `𝒯` is an immersion as soon as the relative diagonal of
`q : 𝒴 ⟶ 𝒯` is. -/
theorem isImmersion_graph_of_isImmersion_relativeDiagonal
    (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒯.val q.hom)) :
    IsImmersion B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsImmersion B S hS k.hom) g p q η
    (isImmersion_comparison_of_isImmersion_relativeDiagonal B S hS g (𝟙 𝒴) q hq)

/-- A section of `f : 𝒳 ⟶ 𝒯` is an immersion as soon as the relative diagonal of `f` is. -/
theorem isImmersion_section_of_isImmersion_relativeDiagonal
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒯.val f.hom)) :
    IsImmersion B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsImmersion B S hS k.hom) f s η
    (isImmersion_graph_of_isImmersion_relativeDiagonal B S hS s (𝟙 𝒯) f η.symm hf)

/-- Let `f : 𝒳 ⟶ 𝒯` be a 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces and locally separated in the sense of Properties of Stacks, Section 04XB. Then
every section of `f` is an immersion in that sense. -/
theorem isImmersion_section_of_isLocallySeparated
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsLocallySeparated B S hS f.hom) :
    IsImmersion B S hS s.hom :=
  isImmersion_section_of_isImmersion_relativeDiagonal B S hS f s hs
    ((isLocallySeparated_iff_isImmersion_relativeDiagonal B S hS f hf).mp h)

end Section

/-! ### Stacks 0CL0, part (3), conditions (a) and (b) -/

section Inertia

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- Local separatedness of a 1-morphism `q` to `𝒳` passes to `p : 𝒵' ⟶ 𝒳` along an equivalence
`a : 𝒵' ⟶ 𝒵` over `𝒳` between the sources. -/
private theorem isLocallySeparated_of_equivalence {𝒵 𝒵' : AlgebraicStacks.{u, w} B S hS}
    (p : 𝒵' ⟶ 𝒳) (q : 𝒵 ⟶ 𝒳) (a : 𝒵'.val.val ⥤ᵇ 𝒵.val.val)
    (ha : BasedFunctor.comp a q.hom.hom = p.hom.hom) (he : a.IsEquivalence)
    (h : IsLocallySeparated B S hS q.hom) : IsLocallySeparated B S hS p.hom :=
  @relativeProperty_of_equivalences B S hS _ _ _ _ (Space.locallySeparatedMorphismProperty B S hS)
    p.hom.hom q.hom.hom a (BasedFunctor.id 𝒳.val.val) (eqToIso ha)
    he (isEquivalence_basedFunctorId B S hS 𝒳.val) h

/-- The relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is locally separated in the sense of
Properties of Stacks, Section 04XB exactly when the first projection of the 2-fibre product of
`Δ_f` with itself is. -/
theorem isLocallySeparated_relativeInertiaProjection_iff_twoFibreProductFst (f : 𝒳 ⟶ 𝒴) :
    IsLocallySeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsLocallySeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom :=
  ⟨isLocallySeparated_of_equivalence B S hS _ _
      (secondRelativeDiagonalToRelativeInertia B S hS f.hom).hom
      rfl (isEquivalence_secondRelativeDiagonalToRelativeInertia B S hS f.hom),
    isLocallySeparated_of_equivalence B S hS _ _
      (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
      rfl (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)⟩

/-- The first projection of the 2-fibre product of `Δ_f` with itself is representable by
algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
    𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the relative inertia projection
`π : I_{𝒳/𝒴} ⟶ 𝒳` is locally separated, in the relative sense of Properties of Stacks,
Section 04XB, exactly when the first relative diagonal `Δ_{f, 1} = Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`
is. -/
@[stacks 0CL0 "part (3), conditions (a) and (b): the relative diagonal is locally separated \
exactly when the first projection of the relative inertia is"]
theorem isLocallySeparated_relativeInertiaProjection_iff_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsLocallySeparated B S hS (relativeInertiaProjection B S hS f).hom ↔
      IsLocallySeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  (isLocallySeparated_relativeInertiaProjection_iff_twoFibreProductFst B S hS f).trans
    ⟨fun h => (isLocallySeparated_iff_isImmersion_relativeDiagonal B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).mpr
      (isImmersion_section_of_isLocallySeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)
          (relativeDiagonalAlgebraicStacks B S hS f)).fst
        (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f))
        ⟨eqToIso rfl⟩
        (isRepresentableByAlgebraicSpaces_twoFibreProductFst_relativeDiagonal B S hS f) h),
      fun h => relativeProperty_baseChange.{u, u, u + 1} B S hS
        (Space.locallySeparatedMorphismProperty B S hS)
        𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (relativeDiagonalAlgebraicStacks B S hS f).hom
          (relativeDiagonalAlgebraicStacks B S hS f).hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (relativeDiagonalAlgebraicStacks B S hS f).hom
          (relativeDiagonalAlgebraicStacks B S hS f).hom) h⟩

end Inertia

end AlgebraicGeometry.Stack

end
