module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleAlgClosedEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphismEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed geometric fibre over a strictly henselian local ring

Let `C` be a henselian local ring with separably closed residue field `κ`, let `X ⟶ Spec C` be
proper and let `Spec K ⟶ Spec C` be a geometric point lying over the closed point. Then base
change along the closed geometric fibre `X_K ⟶ X` is an equivalence on finite étale covers.

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_comp` — base change along
  `X ×_S W ⟶ X` is an equivalence when it is one along `X ×_S Z ⟶ X` and along
  `(X ×_S Z) ×_Z W ⟶ X ×_S Z`.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isSepClosed` —
  for `κ` separably closed and `K ⊇ κ` algebraically closed, base change along `Y_K ⟶ Y` is an
  equivalence for every `Y` proper over `κ`.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_henselianLocalRing` —
  the closed geometric fibre of a proper scheme over a strictly henselian local ring.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap` — the same,
  for the geometric fibre `X_{s̄} ⟶ X ×_S Spec C` of a proper `X ⟶ S`, the form in which the
  construction of specialization maps uses it.

## Implementation notes

The proof is the one in the source. Since the geometric point lies over the closed point, it
factors as `Spec K ⟶ Spec κ ⟶ Spec C`, and `X_K ⟶ X` factors as `X_K ⟶ X_κ ⟶ X`. The second map
is Stacks 0A48 (`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`). For the
first, let `L` be the algebraic closure of `κ` in `K`: it is algebraically closed, and purely
inseparable over `κ` because `κ` is separably closed. So `X_K ⟶ X_κ` factors as
`X_K ⟶ X_L ⟶ X_κ`, the first of which is Stacks 0A49 for the extension `L ⊆ K` of algebraically
closed fields and the second Stacks 0BTW (here `L` is the perfection of `κ`).

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0BTW](https://stacks.math.columbia.edu/tag/0BTW)
* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Base change along `X ×_S W ⟶ X`, for `W ⟶ Z ⟶ S`, is an equivalence on finite étale covers
as soon as base change along `X ×_S Z ⟶ X` and along `(X ×_S Z) ×_Z W ⟶ X ×_S Z` are: up to the
isomorphism `pullbackLeftPullbackSndIso`, the first projection is the composite of the other
two. -/
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_comp {X S Z W : Scheme.{u}}
    (f : X ⟶ S) (b : Z ⟶ S) (a : W ⟶ Z)
    (hb : (finiteEtaleBaseChange (pullback.fst f b)).IsEquivalence)
    (ha : (finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a)).IsEquivalence) :
    (finiteEtaleBaseChange (pullback.fst f (a ≫ b))).IsEquivalence := by
  have hcomp : (finiteEtaleBaseChange
      (pullback.fst (pullback.snd f b) a ≫ pullback.fst f b)).IsEquivalence :=
    have : (finiteEtaleBaseChange (pullback.fst f b) ⋙
        finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a)).IsEquivalence :=
      Functor.isEquivalence_trans _ _
    Functor.isEquivalence_of_iso (finiteEtaleBaseChangeComp _ _).symm
  rw [← pullbackLeftPullbackSndIso_inv_fst f b a]
  exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ hcomp

/-- For a separably closed field `κ` and an algebraically closed extension `K` of `κ`, base
change along `Y_K ⟶ Y` is an equivalence on finite étale covers for every proper `Y` over `κ`.

With `L` the algebraic closure of `κ` in `K`, the map factors as `Y_K ⟶ Y_L ⟶ Y`: the first is
Stacks 0A49 for the algebraically closed fields `L ⊆ K`, the second Stacks 0BTW for the purely
inseparable extension `L / κ`. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isSepClosed
    {κ K : Type u} [Field κ] [Field K] [Algebra κ K] [IsSepClosed κ] [IsAlgClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of κ)) [IsProper g] :
    (finiteEtaleBaseChange (pullback.fst g
      (Spec.map (CommRingCat.ofHom (algebraMap κ K))))).IsEquivalence := by
  let L := algebraicClosure κ K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed κ
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap κ K))
      = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap κ L)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have : IsPurelyInseparable κ L := Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  rw [hfac]
  exact isEquivalence_finiteEtaleBaseChange_pullback_fst_comp g _ _
    (finiteEtaleBaseChange_pullbackFst_specMap_algebraMap_isEquivalence κ L g)
    (isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed (k := L) (k' := K)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap κ L)))))

/-- **The closed geometric fibre over a strictly henselian local ring.** Let `C` be a henselian
local ring with separably closed residue field, `h : X ⟶ Spec C` proper, and
`p : Spec K ⟶ Spec C` a point over the closed point with `K` algebraically closed. Then base
change along `X ×_{Spec C} Spec K ⟶ X` is an equivalence on finite étale covers.

The point `p` factors through `Spec (C ⧸ 𝔪)`; base change to the closed fibre is Stacks 0A48,
and from the closed fibre to `X_K` it is
`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isSepClosed`. -/
@[sga "3 X 4.0" "special case",
  sga "4 XII 5.9bis" "special case",
  sga "4½ Arcata 4.2.2" "special case",
  sga "7 IX 2.2.4" "special case"]
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_of_henselianLocalRing
    (C : Type u) [CommRing C] [HenselianLocalRing C] [IsSepClosed (ResidueField C)]
    {X : Scheme.{u}} (h : X ⟶ Spec (.of C)) [IsProper h] {K : Type u} [Field K] [IsAlgClosed K]
    (p : Spec (.of K) ⟶ Spec (.of C)) (hp : p (closedPoint K) = closedPoint C) :
    (finiteEtaleBaseChange (pullback.fst h p)).IsEquivalence := by
  let φ : C →+* K := (Spec.preimage p).hom
  have hker : maximalIdeal C ≤ RingHom.ker φ := by
    intro x hx
    have h' : (maximalIdeal K).comap φ = maximalIdeal C := by
      rw [← Spec.map_preimage p] at hp
      exact congrArg PrimeSpectrum.asIdeal hp
    rw [← h'] at hx
    simpa [RingHom.mem_ker] using hx
  let _ : Algebra (ResidueField C) K := (Ideal.Quotient.lift _ φ hker).toAlgebra
  have hpfac : p = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField C) K)) ≫
      Spec.map (CommRingCat.ofHom (residue C)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    conv_lhs => rw [← Spec.map_preimage p]
    rfl
  rw [hpfac]
  exact isEquivalence_finiteEtaleBaseChange_pullback_fst_comp h _ _
    (isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing C h)
    (isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isSepClosed
      (pullback.snd h (Spec.map (CommRingCat.ofHom (residue C)))))

/-- **The closed geometric fibre of a proper morphism over a strictly henselian local ring.**
Let `f : X ⟶ S` be proper, `s̄` a geometric point of `S`, `C` a henselian local ring with
separably closed residue field, `r : Spec C ⟶ S`, and `p : s̄ ⟶ Spec C` a factorization of `s̄`
through the closed point of `Spec C`. Then base change along `X_{s̄} ⟶ X ×_S Spec C` is an
equivalence on finite étale covers. -/
@[sga "4 XII 5.9bis" "special case", sga "4 XIII 1.1" "partial"]
theorem isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : GeometricPoint S)
    (C : Type u) [CommRing C] [HenselianLocalRing C] [IsSepClosed (ResidueField C)]
    (r : Spec (.of C) ⟶ S) (p : s.source ⟶ Spec (.of C)) (hp : p ≫ r = s.hom)
    (hpclosed : p (closedPoint s.residueField) = closedPoint C) :
    (finiteEtaleBaseChange (fiberOverGeometricPointMap f s r p hp)).IsEquivalence := by
  have he : fiberOverGeometricPointMap f s r p hp
      = ((pullback.congrHom rfl hp.symm).hom ≫ (pullbackLeftPullbackSndIso f r p).inv) ≫
        pullback.fst (pullback.snd f r) p := by
    refine pullback.hom_ext ?_ ?_
    · simp only [fiberOverGeometricPointMap, pullback.map, Category.comp_id, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom]
      rw [pullback.lift_fst, pullback.lift_fst]
    · simp only [fiberOverGeometricPointMap, pullback.map, Category.comp_id, Category.assoc,
        pullback.congrHom_hom]
      rw [pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd]
  rw [he]
  exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _
    (isEquivalence_finiteEtaleBaseChange_pullback_fst_of_henselianLocalRing C
      (pullback.snd f r) p hpclosed)

end AlgebraicGeometry

end
