module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitEtaleChartSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpacesCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitThickeningChartAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitThickeningChartSize
public import StacksFrontier.CategoryTheory.Filtered.UpSetCofinal

/-!
# A directed colimit of algebraic spaces along thickenings is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and `E : Λ ⥤ FppfSheaf B S hS` a directed
system of algebraic spaces over `S` whose transition morphisms are representable thickenings.
**Stacks 0AIU** states that `colim E` is a formal algebraic space. As printed this is false:
the colimit need not satisfy the set-theoretic condition of **Stacks 0AIS**, which Definition
0AIM asks of a formal algebraic space
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_thickenings`). This
file proves the corrected statement: a sheaf isomorphic to `colim E` which satisfies the
set-theoretic condition is a formal algebraic space. No other hypothesis is added.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`:
  the corrected Stacks 0AIU.

## Implementation notes

The proof is the source's. Fix a stage `o` and pass to the cofinal up-set `{j // o ≤ j}`, over
which `o` is a least element. The affine étale charts `U_k ⟶ E o` of an atlas of `E o`
(`AlgebraicGeometry.FormalSpace.exists_affine_etale_charts_of_isAlgebraicSpaceULift`) are
transported to every stage `E j` (`AlgebraicGeometry.FormalSpace.thickeningChart`, Stacks 05ZH),
where they are affine (Stacks 07VT, thickening case), equifibered over `E` and cover each
stage (`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_thickeningChartπ_app`).
Their base changes along points of a stage are bounded uniformly
(`AlgebraicGeometry.FormalSpace.exists_isPullback_thickeningChartπ_app_size_le`), so the
colimit of each transported chart is representable étale over the colimit
(`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_etale_over_affinePoints`); hence it
satisfies the set-theoretic condition and is an affine formal algebraic space by Stacks 0GVM
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_thickeningChart`). The
chart-system criterion `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleChartSystem`
concludes.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FormalSpace.CartesianColimit (equifibered_colimit_isPullback)

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIU, corrected.** Let `E` be a directed system of algebraic spaces over `S` whose
transition morphisms are representable thickenings. A sheaf `Z` isomorphic to `colim E` which
satisfies the set-theoretic condition of Stacks 0AIS is a formal algebraic space over `S`.

The set-theoretic condition cannot be dropped: without it the statement is false
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_thickenings`). -/
@[stacks 0AIU "corrected form: the printed statement is false, the colimit need not satisfy \
the set-theoretic condition of Stacks 0AIS that Definition 0AIM asks of a formal algebraic space \
(AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_thickenings); stated \
for a sheaf isomorphic to the colimit which satisfies that condition, under the source's \
hypotheses otherwise"]
theorem isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (halg : ∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨eZ⟩ := hZ
  have o : Λ := Nonempty.some ‹Nonempty Λ›
  -- the up-set of `o`, over which `o` is a least element
  set E' : {j : Λ // o ≤ j} ⥤ FppfSheaf B S hS := CategoryTheory.upSetInclusion o ⋙ E
    with hE'def
  set o' : {j : Λ // o ≤ j} := ⟨o, le_refl o⟩ with ho'def
  have ho' : ∀ i : {j : Λ // o ≤ j}, o' ≤ i := fun i ↦ i.2
  have halg' : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E'.obj i).obj := fun i ↦ halg i.1
  have hthick' : ∀ ⦃i j : {j : Λ // o ≤ j}⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E'.map g).hom := fun _ _ g ↦
    hthick ((CategoryTheory.upSetInclusion o).map g)
  have hmono : ∀ ⦃i j : {j : Λ // o ≤ j}⦄ (g : i ⟶ j), Mono (E'.map g) := fun _ _ g ↦
    have := mono_of_isRepresentableThickeningULift B S hS (hthick' g)
    Sheaf.Hom.mono_of_presheaf_mono J _ (E'.map g)
  -- the colimit over the up-set is the colimit over `Λ`
  obtain ⟨hc⟩ := CategoryTheory.nonempty_isColimit_whiskerLeft_upSetInclusion o
    (colimit.isColimit E)
  let eZ' : Z ≅ colimit E' := eZ.trans (hc.coconePointUniqueUpToIso (colimit.isColimit E'))
  -- affine étale charts of the least stage, jointly surjective on points
  obtain ⟨I, U, uk, hUaff, hu, hpts⟩ :=
    exists_affine_etale_charts_of_isAlgebraicSpaceULift B S hS (halg' o')
  let G : I → ({j : Λ // o ≤ j} ⥤ FppfSheaf B S hS) := fun k ↦
    thickeningChart B S hS E' hthick' o' ho' (uk k) halg' (hu k)
  let α : ∀ k, G k ⟶ E' := fun k ↦ thickeningChartπ B S hS E' hthick' o' ho' (uk k) halg' (hu k)
  let f : I → Cardinal.{u} → Cardinal.{u} := fun k s ↦
    (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max ((BigFppfOver.toScheme B S hS).obj (U k)).size s
  have hfmono : ∀ k, Monotone (f k) := fun k ↦ monotone_two_pow_two_pow_max _
  have hf : ∀ k, ∀ s < B.cutoff, f k s < B.cutoff := fun k ↦
    two_pow_two_pow_max_lt_cutoff B (U k).left.property
  have hαet : ∀ (k : I) (i : {j : Λ // o ≤ j}) (X : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
      ∀ ξ : J.uliftYoneda.{u + 1}.obj X ⟶ E'.obj i,
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ X) (c : J.uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c (J.uliftYoneda.{u + 1}.map pr) ((α k).app i) ξ ∧
        Etale ((BigFppfOver.toScheme B S hS).map pr) ∧
        ((BigFppfOver.toScheme B S hS).obj W).size ≤
          f k ((BigFppfOver.toScheme B S hS).obj X).size := fun k i X _ ξ ↦
    exists_isPullback_thickeningChartπ_app_size_le B S hS E' hthick' o' ho' halg' (uk k) (hu k)
      i X ξ
  have hα : ∀ k, (α k).Equifibered := fun k ↦
    thickeningChartπ_equifibered B S hS E' hthick' o' ho' (uk k) halg' (hu k)
  -- the colimit of each chart diagram is representable by algebraic spaces over `Z`
  have hrep : ∀ k, IsRepresentableEtale B S hS (colimMap (α k) ≫ eZ'.inv) := by
    intro k
    have hsq : ∀ i, IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k))
        (colimit.ι E' i) := by
      intro i
      have _ : IsConnected (Under i) := IsFiltered.isConnected _
      exact equifibered_colimit_isPullback (α k) (hα k) i
    refine isRepresentableEtale_of_etale_over_affinePoints B S hS
      (colimMap (α k) ≫ eZ'.inv) (f k) (hfmono k) (hf k) fun X hX ξ ↦ ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj X) := hX
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj X) := inferInstance
    obtain ⟨i, ξ', hξ'⟩ :=
      exists_factor_through_stage_of_compact B S hS E' hmono X (ξ ≫ eZ'.hom)
    obtain ⟨W, pr, c, hpb, het, hsize⟩ := hαet k i X hX ξ'
    refine ⟨W, pr, c ≫ colimit.ι (G k) i, ?_, het, hsize⟩
    have hpaste : IsPullback (c ≫ colimit.ι (G k) i)
        (J.uliftYoneda.{u + 1}.map pr) (colimMap (α k)) (ξ' ≫ colimit.ι E' i) :=
      hpb.paste_horiz (hsq i)
    rw [← hξ'] at hpaste
    exact hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ'.symm
      (by simp) (by simp; rfl) (by simp) (by simp)
  have haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)) := fun k ↦
    isAffineFormalAlgebraicSpace_colimit_thickeningChart B S hS E' hthick' o' ho' halg'
      (hUaff k) (uk k) (hu k) hZset (colimMap (α k) ≫ eZ'.inv) (hrep k).1
  exact isFormalAlgebraicSpace_of_etaleChartSystem B S hS E' hmono G α haff f hfmono hf hαet hα
    (fun i ↦ isLocallySurjective_sigmaDesc_thickeningChartπ_app B S hS E' hthick' o' ho' halg'
      U hUaff uk hu hpts i) Z hZset ⟨eZ'⟩

end AlgebraicGeometry.FormalSpace

end
