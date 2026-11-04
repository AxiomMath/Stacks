module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget
import all StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
import all StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget

/-!
# The size of the scheme representing morphisms out of a finite locally free scheme

Stacks 0BL4 (`Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable`) represents the functor
of `S`-morphisms from a finite locally free `Z ⟶ S` to `X` by a scheme glued from affine charts.
This file bounds the size of that scheme by the sizes of `S` and of `X`, which is what places it
in a big site containing `S` and `X`.

## Main results

* `Stacks.Morphisms.homFromFiniteLocallyFree_representableBy_size_le`: Stacks 0BL4 with the size
  of the representing scheme bounded by `max ℵ₀ (max S.size X.size)`.

## Implementation notes

The representing scheme is glued from the affine charts of
`Stacks.Morphisms.affineChartRepresentingData`, of which there are at most as many as pairs of
affine opens of `S` and of `X`. Each chart represents the same functor as the affine scheme of
bounded size of Stacks 05Y6 over the chart (in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget`), so it is isomorphic
to it and has the same size.

## References

* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites (totalPresheaf)

universe u

namespace Stacks.Morphisms

/-- The index set of the affine charts injects into pairs of affine opens of the base and of
`X`, the remaining fields being propositions. -/
private lemma affineChartIndex_injective {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) :
    Function.Injective (fun i : AffineChartIndex f g ↦
      ((⟨i.V, i.hV⟩ : S.affineOpens), (⟨i.U, i.hU⟩ : X.affineOpens))) := by
  intro i j h
  obtain ⟨hV, hU⟩ := Prod.mk.inj h
  cases i
  cases j
  cases congrArg Subtype.val hV
  cases congrArg Subtype.val hU
  rfl

/-- The scheme of an affine chart is of size at most the larger of the sizes of `S` and of `X`:
it represents the same functor as the affine scheme of bounded size given by Stacks 05Y6 over
the chart. -/
private lemma affineChartRepresentingData_size_le {S Z X : Scheme.{u}}
    (f : Z ⟶ S) (g : X ⟶ S) [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    (affineChartRepresentingData f g i).1.size ≤ max S.size X.size := by
  have : IsFiniteLocallyFree (pullback.fst i.V.ι f) := isFiniteLocallyFree_pullback_fst f i.V.ι
  have : IsAffine i.V.toScheme := i.hV
  have : IsAffine i.U.toScheme := i.hU
  have : IsAffine (pullback i.V.ι f) := isAffine_of_isAffineHom (pullback.fst i.V.ι f)
  obtain ⟨W, -, hW, ⟨r⟩⟩ :=
    AlgebraicGeometry.RelativeHomAffineTarget.relativeHom_representableBy_affine_size_le
      i.V.toScheme (pullback i.V.ι f) i.U.toScheme (pullback.fst i.V.ι f)
      (affineChartMapToBase i) i.hfinite i.hfree
  let e := (affineChartRepresentingData f g i).2.uniqueUpToIso
    (totalRepresentableBy (r.ofIso (pullbackHomIso _ _)))
  rw [Scheme.size_congr e]
  exact hW.trans (max_le_max (Scheme.size_coe_opens_le S i.V) (Scheme.size_coe_opens_le X i.U))

/-- **Stacks Project, Tag 0BL4, with the size of the representing scheme.** If `Z` is finite
locally free over `S` and every finite set of points in a fibre of `X` lies in an affine open of
`X`, then the functor of `S`-morphisms from `Z` to `X` is represented by a scheme over `S` whose
size is bounded by the sizes of `S` and of `X`.

The representing scheme is glued from the affine charts of
`Stacks.Morphisms.affineChartRepresentingData`, of which there are at most as many as pairs of
affine opens of `S` and of `X`, and each of which is of size at most that of `S` and of `X` by
Stacks Tag 05Y6. -/
theorem homFromFiniteLocallyFree_representableBy_size_le
    {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f]
    (hX : ∀ (s : S) (t : Set X), t.Finite →
      (∀ x ∈ t, g.base x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U) :
    ∃ M : Over S, M.left.size ≤ max Cardinal.aleph0 (max S.size X.size) ∧
      Nonempty
        (((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).RepresentableBy M) := by
  let H := totalPresheaf (pullbackHom f g)
  let F : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨H, (isSheaf_iff_isSheaf_of_type _ _).2 (totalPullbackHom_isSheaf f g)⟩
  let := affineCharts_locallySurjective f g hX
  let hf := affineChartToTotal_open f g
  let R := Scheme.LocalRepresentability.representableBy (F := F) (f := affineChartToTotal f g) hf
  have : (pullbackHom f g).IsRepresentable := representable_of_totalRepresentable R
  let rep := (pullbackHom f g).representableBy
  refine ⟨(pullbackHom f g).reprX, ?_, ⟨rep.ofIso (pullbackHomIso f g).symm⟩⟩
  rw [Scheme.size_congr ((totalRepresentableBy rep).uniqueUpToIso R)]
  let D := Scheme.LocalRepresentability.glueData (F := F) (f := affineChartToTotal f g) hf
  let κ := max Cardinal.aleph0 (max S.size X.size)
  have hκ : Cardinal.aleph0 ≤ κ := le_max_left _ _
  -- the charts are of size at most `κ`
  have hchart : ∀ i, (D.U i).size ≤ κ := fun i ↦
    (affineChartRepresentingData_size_le f g i).trans (le_max_right _ _)
  -- there are at most `κ` of them
  have hindex : Cardinal.mk (AffineChartIndex f g) ≤ κ := by
    refine (Cardinal.mk_le_of_injective (affineChartIndex_injective f g)).trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    refine (Cardinal.mul_le_max _ _).trans (max_le (max_le ?_ ?_) hκ)
    · exact S.mk_affineOpens_le_size.trans (le_max_of_le_right (le_max_left _ _))
    · exact X.mk_affineOpens_le_size.trans (le_max_of_le_right (le_max_right _ _))
  rcases isEmpty_or_nonempty (AffineChartIndex f g) with hI | hI
  · exact (size_le_aleph0_of_isEmpty _ ⟨fun x ↦ hI.false (D.openCover.idx x)⟩).trans hκ
  · have : Nonempty D.J := hI
    exact (scheme_glueData_size_le D).trans (max_le hindex (ciSup_le' hchart))

end Stacks.Morphisms

end
