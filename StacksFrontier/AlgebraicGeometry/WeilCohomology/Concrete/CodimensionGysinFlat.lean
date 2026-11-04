module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.RankOne
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit

/-!
# The Gysin map of a flat morphism on classes of closed subschemes

Let `f : X ⟶ Y` be a flat morphism of schemes smooth over a field `k`, with `X` and `Y` of constant
dimensions `d` and `e` and `f` of relative dimension `t = d - e`. For a closed subscheme `Z ⊂ Y`
of codimension at least `c`, the Gysin map of Stacks 0FF3, graded by codimension
(`Stacks.Chow.codimensionGysin`), carries the class `[Z] ∈ CH^c(Y)` to the class
`[X ×_Y Z] ∈ CH^c(X)` of its scheme-theoretic inverse image:

  `f^![Z] = [f⁻¹Z]`.

On each piece of `X` the Gysin map of the flat morphism `f` is flat pullback (Stacks 0FF4,
`Stacks.Chow.dimPartPieceGysin_heq_flatPullbackChow`), restriction to an open subscheme is flat
pullback in relative dimension zero, flat pullbacks compose (Stacks 02RD), and flat pullback
carries `[Z]` to `[f⁻¹Z]` (Stacks 02RB).

## Main results

* `Stacks.Chow.codimensionGysin_closedSubschemeClass_of_flat` — `f^![Z] = [f⁻¹Z]`.

## References

* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart isEmpty_dimPart_of_ne closedSubschemeClass
  closedSubschemeClass_apply)

/-- Flat pullback on Chow groups respects equalities of the morphism and of its relative
dimension. -/
theorem flatPullbackChow_heq_of_morphism_eq {C : ChowSituation.{u}} {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {g g' : X' ⟶ X} [LocallyOfFiniteType g] [Flat g] [LocallyOfFiniteType g'] [Flat g']
    (hgg : g = g') (hbase : g ≫ sX = sX') (hbase' : g' ≫ sX = sX') {r r' : ℕ} (hr : r = r')
    (hg : AlgebraicGeometry.RelativeDimension g r)
    (hg' : AlgebraicGeometry.RelativeDimension g' r') (m : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX g hbase r hg m)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sX' sX g' hbase' r' hg' m)
    (x : chowGroup C sX m) :
    flatPullbackChow C sX' sX g hbase r hg m hfac x ≍
      flatPullbackChow C sX' sX g' hbase' r' hg' m hfac' x := by
  subst hgg hr
  rfl

variable {k : Type u} [Field k]

/-- Restriction of Chow classes along an open immersion, as a heterogeneous equality with flat
pullback in relative dimension zero. -/
theorem chowGroupRestrict_heq_flatPullbackChow {X U : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sU : U ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) (m : ℤ) (α : chowGroup (fieldChowSituation k) sX m) :
    chowGroupRestrict (fieldChowSituation k) sX sU j hj m α ≍
      flatPullbackChow (fieldChowSituation k) sU sX j hj 0 (relativeDimension_of_isOpenImmersion j)
        m (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α := by
  rw [← cast_flatPullbackChow_eq_chowGroupRestrict (fieldChowSituation k) sX sU j hj (k := m)
    (by simp) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α]
  exact eqRec_heq _ _

section Flat

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX)

/-- **`f^![Z] = [f⁻¹Z]` for a flat morphism `f`** of schemes smooth over `k`, of constant
dimensions `d` and `e`, with `f` of relative dimension `t = d - e`: the Gysin map of Stacks 0FF3,
graded by codimension, carries the class of a closed subscheme `Z ⊂ Y` of codimension at least `c`
to the class of its scheme-theoretic inverse image `X ×_Y Z`. For flat `f` the Gysin map is flat
pullback (Stacks 0FF4, on the pieces of `X`: `dimPartPieceGysin_heq_flatPullbackChow`), and flat
pullback carries `[Z]` to `[f⁻¹Z]` (Stacks 02RB). -/
theorem codimensionGysin_closedSubschemeClass_of_flat {d e t : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension sX d)
    (hY : AlgebraicGeometry.RelativeDimension sY e)
    (ht : AlgebraicGeometry.RelativeDimension f t) (htd : t + e = d) {Z : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (c : ℤ)
    (hZ : schemeDeltaDimension (fieldChowSituation k) (i ≫ sY) ≤ (((e : ℤ) - c : ℤ) : EInt)) :
    codimensionGysin sX sY hf c (closedSubschemeClass sY i c) =
      closedSubschemeClass sX (pullback.fst f i) c := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  swap
  · have := isEmpty_dimPart_of_ne sX hX hd
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX d')
      ((d' : ℤ) - c)
    exact Subsingleton.elim _ _
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d' ((d' : ℤ) - c)).injective
    (funext fun e' ↦ ?_)
  obtain ⟨e'⟩ := e'
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  rcases eq_or_ne e' e with rfl | he
  swap
  · have hemp := isEmpty_dimPart_of_ne sY hY he
    have : IsEmpty (dimPartPiece sX sY f d' e').toScheme :=
      ⟨fun w ↦ hemp.false ⟨_, w.2⟩⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase sX sY f d' e') ((d' : ℤ) - c)
    exact Subsingleton.elim _ _
  -- the restriction `q = f_{d,e} : X_{d,e} ⟶ Y_e` is flat of relative dimension `t`
  have hres : AlgebraicGeometry.RelativeDimension (f ∣_ dimPart sY e') t :=
    AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_morphismRestrict f (dimPart sY e')).flip ht
  have hq : AlgebraicGeometry.RelativeDimension (dimPartPieceHom sX sY f d' e') t :=
    AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion _ _ hres
  have : Flat (dimPartPieceHom sX sY f d' e') := by
    dsimp only [dimPartPieceHom]; infer_instance
  have hra : AlgebraicGeometry.RelativeDimension
      ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) 0 :=
    relativeDimension_of_isOpenImmersion _
  have ha : ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ≫ sX =
      dimPartPieceBase sX sY f d' e' := by
    rw [Category.assoc]
  have hqa : dimPartPieceHom sX sY f d' e' ≫ (dimPart sY e').ι =
      ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ≫ f := by
    rw [dimPartPieceHom_ι, Category.assoc]
  -- `f^! = q^*` on the piece
  have h1 := dimPartPieceGysin_heq_flatPullbackChow sX sY hf d' e' c hq htd
    (closedSubschemeClass sY i c e')
  rw [closedSubschemeClass_apply] at h1
  -- the class of `Z` before restriction to `Y_e`
  let cls : chowGroup (fieldChowSituation k) sY ((e' : ℤ) - c) :=
    QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY i
      ((e' : ℤ) - c))
  -- restriction to `Y_e` is flat pullback along its inclusion
  have h2 := flatPullbackChow_heq_of_heq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') (partBase sY e') (dimPartPieceHom sX sY f d' e')
    (dimPartPieceHom_comp_partBase sX sY hf d' e') t hq (add_zero ((e' : ℤ) - c)).symm
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (chowGroupRestrict_heq_flatPullbackChow sY (partBase sY e') (dimPart sY e').ι rfl
      ((e' : ℤ) - c) cls)
  -- `q^* ∘ ι_e^* = (q ≫ ι_e)^*`
  have h3 := flatPullbackChow_comp (fieldChowSituation k) (dimPartPieceBase sX sY f d' e')
    (partBase sY e') sY (dimPartPieceHom sX sY f d' e') (dimPart sY e').ι
    (dimPartPieceHom_comp_partBase sX sY hf d' e') rfl t 0 hq
    (relativeDimension_of_isOpenImmersion (dimPart sY e').ι) ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    cls
  -- `q ≫ ι_e = (ι_{X_{d,e}} ≫ ι_{X_d}) ≫ f`
  have h4 := flatPullbackChow_heq_of_morphism_eq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') sY hqa
    (by rw [Category.assoc]; exact dimPartPieceHom_comp_partBase sX sY hf d' e')
    (by rw [Category.assoc, hf, ha]) (by omega : t + 0 = 0 + t)
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ _ hq
      (relativeDimension_of_isOpenImmersion (dimPart sY e').ι))
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ f hra ht) ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    cls
  -- `(a ≫ f)^* = a^* ∘ f^*`
  have h5 := flatPullbackChow_comp (fieldChowSituation k) (dimPartPieceBase sX sY f d' e')
    sX sY _ f ha hf 0 t hra ht ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    cls
  -- `f^*[Z] = [f⁻¹Z]`
  have h6 :=
    Stacks.WeilCohomology.flatPullbackChow_mk_cycleAssociatedToClosedSubscheme sX sY f hf t ht i
      ((e' : ℤ) - c) hZ (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
  -- the right side, read as a flat pullback to the piece
  rw [closedSubschemeClass_apply sX (pullback.fst f i) c d', chowGroupRestrict_comp]
  have h7 := chowGroupRestrict_heq_flatPullbackChow sX (dimPartPieceBase sX sY f d' e')
    ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ha ((d' : ℤ) - c)
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
      (pullback.fst f i) ((d' : ℤ) - c)))
  have h8 := flatPullbackChow_heq_of_heq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') sX _ ha 0 hra (by omega : (d' : ℤ) - c = (e' : ℤ) - c + t)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    ((mk_cycleAssociatedToClosedSubscheme_heq (fieldChowSituation k) sX (pullback.fst f i)
      (by omega : (d' : ℤ) - c = (e' : ℤ) - c + t)).trans (heq_of_eq h6.symm))
  exact eq_of_heq (h1.trans (h2.trans (h3.trans (h4.trans (h5.symm.trans
    (h8.symm.trans h7.symm))))))

end Flat

end Stacks.Chow

end
