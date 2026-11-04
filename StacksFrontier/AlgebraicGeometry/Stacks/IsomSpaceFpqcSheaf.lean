module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace

/-!
# Isomorphism spaces of an algebraic stack are sheaves for the fpqc topology

Let `𝒳` be an algebraic stack over a scheme `S` and let `x`, `y` be objects of the fibre of `𝒳`
over a scheme `U` over `S`. Then `Isom(x, y)`, read as a presheaf on the big fppf site of `U`, is
a sheaf for the fpqc topology.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack`: the isomorphism
  presheaves of an algebraic stack are algebraic spaces, which is condition (2) of Stacks 045G.
* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_univ`: the same for
  a category fibred in groupoids whose total category has arbitrary morphism and object universes.
* `AlgebraicGeometry.Stack.isSheaf_fpqc_isomSpace_of_isAlgebraicStack`: those presheaves are
  sheaves for the fpqc topology on the big fppf site of `U`.
* `AlgebraicGeometry.Stack.isMorSheaf_fpqc_of_isAlgebraicStack`: **the full-faithfulness half of
  Stacks 0GRH**, i.e. condition (2) of the fpqc stack condition.

## Implementation notes

The isomorphism presheaf is an algebraic space because the diagonal of an algebraic stack is
representable by algebraic spaces, which is the equivalence of conditions (1) and (2) of
Stacks 045G; an algebraic space is a sheaf for the fpqc topology by Stacks 0APL. The comparison
isomorphism of Stacks 045G is stated after a universe lift on both sides, and the sheaf condition
for a `Type`-valued presheaf is invariant under such a lift
(`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`), so no universe restriction is incurred.

The passage from the big fppf site of `U` to the localization at `U` of the big fppf site of `S`
is the iterated-slice equivalence: the fpqc topology on either is a localization of the fpqc
topology on `Sch_κ` (`AlgebraicGeometry.BigFppfOver.fpqcTopology_eq_over`), and the forward
functor of that equivalence is continuous for the two localizations.

Only the first half of the proof of Stacks 0GRH is formalized here. Its second half, the
effectivity of fpqc descent data, needs Stacks 0247 for a descent datum on schemes relative to an
fpqc covering family; the library has 0247 only as effective descent along a surjective étale
chart of the site, and the family-shaped effectivity it has for ind-quasi-affine morphisms,
Stacks 0APK, is restricted to an affine base.

The diagonal hypothesis of the source is not needed for this half: representability of the
diagonal by algebraic spaces, which every algebraic stack has, already makes `Isom(x, y)` an
algebraic space.

## References

* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The isomorphism presheaves of an algebraic stack are algebraic spaces, in any universes. -/
private theorem isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_aux.{v, t}
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  obtain ⟨hg, -, hdiag, -⟩ := h𝒳
  rw [← hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf,
    hasRepresentableDiagonal_iff]
  have he : CatFiberedInGroupoids.mk 𝒳.val hg = 𝒳 := Subtype.ext rfl
  rw [← he]
  exact hdiag

/-- **The isomorphism presheaves of an algebraic stack are algebraic spaces.** This is
condition (2) of Stacks 045G, which holds for an algebraic stack because its diagonal is
representable by algebraic spaces. -/
theorem isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  exact isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_aux B S hS 𝒳 h𝒳

section Univ

universe v t

/-- **The isomorphism presheaves of an algebraic stack are algebraic spaces**, for a category
fibred in groupoids over the big fppf site of `S` whose total category has arbitrary morphism and
object universes, such as a stackification. This is condition (2) of Stacks 045G, which holds for
an algebraic stack because its diagonal is representable by algebraic spaces. -/
theorem isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_univ
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  exact isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_aux B S hS 𝒳 h𝒳

end Univ

/-- **The isomorphism spaces of an algebraic stack are sheaves for the fpqc topology.** For
objects `x`, `y` of the fibre of an algebraic stack over a scheme `U`, the presheaf `Isom(x, y)`
on the big fppf site of `U` satisfies the sheaf condition for every fpqc covering. -/
theorem isSheaf_fpqc_isomSpace_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap
        (BigFppfOver.toScheme B U.left.1 U.left.2)).toGrothendieck)
      (isomSpace B S hS 𝒳 U x y) := by
  obtain ⟨F, hF, ⟨i⟩⟩ := isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack B S hS 𝒳 h𝒳 U x y
  have h0 := hF.isSheaf_fpqc
  rw [isSheaf_iff_isSheaf_of_type] at h0 ⊢
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1
    (Presieve.isSheaf_iso _ i (Presieve.isSheaf_comp_uliftFunctor _ h0))

/-- **The full-faithfulness half of Stacks 0GRH**: condition (2) of the fpqc stack condition for
an algebraic stack. For every scheme `U` over `S` and all objects `x`, `y` of the fibre of an
algebraic stack `𝒳` over `U`, the presheaf `Mor(x, y)` of Stacks 02ZB is a sheaf for the fpqc
topology on the localization at `U`. -/
@[stacks 0GRH "the full-faithfulness half of the proof: condition (2) of the fpqc stack
  condition, that the presheaves Mor(x, y) = Isom(x, y) of an algebraic stack are sheaves for the
  fpqc topology. No hypothesis on the diagonal is carried: representability of the diagonal by
  algebraic spaces, which every algebraic stack has, already suffices for this half, so the
  quasi-affine diagonal of the source and the ind-quasi-affine diagonal of its footnote are both
  dropped. The essential-surjectivity half, effectivity of fpqc descent data, is not formalized."]
theorem isMorSheaf_fpqc_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    haveI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    𝒳.val.p.IsMorSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) U x y := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hiso := isSheaf_fpqc_isomSpace_of_isAlgebraicStack B S hS 𝒳 h𝒳 U x y
  rw [BigFppfOver.fpqcTopology_eq_over] at hiso
  rw [Functor.IsMorSheaf, BigFppfOver.fpqcTopology_eq_over,
    ← Presheaf.isSheaf_of_iso_iff
      (isomPresheafIsoMorPresheaf 𝒳.val.p 𝒳.isFiberedInGroupoids x y),
    ← Presheaf.isSheaf_of_iso_iff
      ((Functor.associator (Over.iteratedSliceForward U).op
          (Over.iteratedSliceBackward U).op (𝒳.val.p.isomPresheaf x y)).symm ≪≫
        Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv U).unitIso)
          (𝒳.val.p.isomPresheaf x y) ≪≫
        (𝒳.val.p.isomPresheaf x y).leftUnitor)]
  have : (Over.iteratedSliceForward U).IsContinuous
      (((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over (B.obj hS)).over U)
      ((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over
        (B.obj (X := U.left.1) U.left.2)) :=
    inferInstanceAs ((Over.iteratedSliceForward U).IsContinuous
      (((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over (B.obj hS)).over U)
      ((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over U.left))
  exact (Over.iteratedSliceForward U).op_comp_isSheaf_of_isSheaf _ _ _ hiso

end AlgebraicGeometry.Stack

end
