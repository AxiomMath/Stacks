module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionBijection
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of the cycle of a module flat only in large dimensions

Let `R` be a discrete valuation ring with fraction field `K` and residue field `kappa`, let
`p : Y ⟶ Spec R` be locally of finite type and let `G` be a quasi-coherent `O_Y`-module of
finite type whose fibrewise supports have dimension at most `r`. Tag 0H4I says that if `G` is
flat over `R` then the specialization map `sp_{Y/R} : Z_r(Y_K) ⟶ Z_r(Y_kappa)` of Section 0H4H
carries `[G_K]_r` to `[G_kappa]_r`, i.e. the member over the generic point of the family
`[G/Y/Spec R]_r` of Tag 0H4Q specializes to its member over the closed point.

This file removes the flatness hypothesis, replacing it by the much weaker condition of
Tag 0CWG that `G` be flat over `R` *in dimensions `≥ r`*: the locus in each fibre where `G`
fails to be flat over the base has dimension `< r`. The argument is the source's own reduction.
Let `U ⊆ Y` be the open locus where `G` is flat over the base — open by Tag 0399, which applies
because `Spec R` is Noetherian, so that `p` is locally of finite presentation and `G`, being
coherent, is of finite presentation. By hypothesis the fibrewise complement of `U` has dimension
`< r`, so every point of a fibre outside `U` has delta-dimension `< r` and therefore restriction
of fibrewise `r`-cycles to `U` is injective (Tag 0H5F). The specialization map commutes with that
restriction, by the open-immersion case of Tag 0H4L, and the restriction of `[G/Y/Spec R]_r` to
`U` is the family of the restricted module, by Tag 0H4R. On `U` the module is honestly flat over
the base, so Tag 0H4I applies there and the two restrictions agree; injectivity of restriction
then gives the formula on `Y`.

## Main results

* `Stacks.Chow.specializationCycle_familyAssociatedToModule_of_isFlatOverInDimensionsGE` — the
  specialization formula of Tag 0H4I under the hypothesis of Tag 0CWG instead of flatness.

## Implementation notes

The statement is a strengthening of Tag 0H4I and is not itself a numbered result of the Stacks
project, so it carries no tag; it is the reduction step inside the proof of Tag 0H56.

Going from the dimension bound `dim T < r` on the non-flat locus of a fibre to the strict
inequality `delta(x) < r` for a point `x` of `T` needs a case distinction on `r`, because the
available input (Tag 02QO) is the non-strict bound `delta(x) ≤ n` from `dim T ≤ n`. For `r = 0`
the hypothesis forces `T` to be empty and there is nothing to prove; for `r = n + 1` it gives
`dim T ≤ n` in `WithBot ℕ∞`, hence `delta(x) ≤ n < r`.

The flatness of the restricted module is phrased with `Scheme.Modules.pullback j` rather than
with `SheafOfModules.restrict j`, these being identified by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, since that is the form in which
Tag 0H4R produces the restricted family. The identification of the restricted family with the
family of the restricted module is made coefficientwise here, rather than by specializing
`Stacks.Chow.familyAssociatedToModule_openRestriction` to the identity open immersion of the
base, so that only the dimension half of Tag 0H4R is used as an input.

## References

* [Stacks Project, Tag 0H4I](https://stacks.math.columbia.edu/tag/0H4I)
* [Stacks Project, Tag 0H56](https://stacks.math.columbia.edu/tag/0H56)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Arithmetic in `WithBot ℕ∞` -/

/-- An element of `WithBot ℕ∞` smaller than `0` is `⊥`. -/
private alias eq_bot_of_lt_zero' := AlgebraicGeometry.eq_bot_of_lt_zero

/-- An element of `WithBot ℕ∞` smaller than the successor of a natural number `m` is at most
`m`. -/
private alias le_natCast_of_lt_natCast_succ' :=
  AlgebraicGeometry.le_natCast_of_lt_natCast_succ

/-- The strict form of Tag 02QO: over a Jacobson base whose dimension function vanishes at
closed points, a point of a closed subset of dimension `< r` has relative dimension `< r`. -/
private theorem relativeDimension_lt_of_mem_of_topologicalKrullDim_lt (C : ChowSituation.{u})
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q] {T : Set Z} (hT : IsClosed T)
    {r : ℕ} (hdim : topologicalKrullDim T < (r : WithBot ℕ∞)) {x : Z} (hx : x ∈ T) :
    relativeDimension C.dimensionFunction q x < (r : ℤ) := by
  match r with
  | 0 =>
    have hbot : topologicalKrullDim ↥T = ⊥ := eq_bot_of_lt_zero' (by simpa using hdim)
    have hempty : IsEmpty ↥T := (topologicalKrullDim_eq_bot_iff_isEmpty _).mp hbot
    exact (hempty.false ⟨x, hx⟩).elim
  | (n + 1) =>
    have hle := relativeDimension_le_of_mem_of_topologicalKrullDim_le C hδ q hT
      (le_natCast_of_lt_natCast_succ' hdim) hx
    have hcast : ((n : ℤ)) < ((n + 1 : ℕ) : ℤ) := by push_cast; omega
    exact lt_of_le_of_lt hle hcast

/-! ### The reduction to an open subscheme -/

/-- The specialization formula of Tag 0H4I holds for a module whose fibrewise supports have
dimension at most `r` as soon as it holds on an open subscheme `j : U ⟶ Y` whose fibrewise
complement has dimension `< r`.

Restriction of fibrewise `r`-cycles to `U` is injective under that dimension hypothesis
(Tag 0H5F), it commutes with the specialization map (the open-immersion case of Tag 0H4L), and
it carries the family associated to the module to the family associated to the restricted module
(Tag 0H4R): the support, the multiplicity and the relative dimension at a point of `U_s` are
those at its image in `X_s`. -/
private theorem specializationCycle_familyAssociatedToModule_of_complementFibreDimensionLT
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y U : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p]
    (pU : U ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType pU] (j : U ⟶ Y)
    [IsOpenImmersion j] (h : j ≫ p = pU) (G : Y.Modules) [G.IsFiniteType] [G.IsQuasicoherent]
    (r : ℕ)
    (hdim : ∀ s : Spec (CommRingCat.of R), topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (p.fiberι s)).obj G)) ≤ (r : WithBot ℕ∞))
    (hcomp : ComplementFibreDimensionLT p pU j h r)
    (hflatU : AlgebraicGeometry.IsFlatOver pU.toLRSHom.toShHom
      ((Scheme.Modules.pullback j).obj G)) :
    specializationCycle p r
        (familyAssociatedToModule p G r hdim (genericPoint (Spec (CommRingCat.of R)))) =
      familyAssociatedToModule p G r hdim (IsLocalRing.closedPoint R) := by
  have h' : j ≫ p = pU ≫ 𝟙 (Spec (CommRingCat.of R)) := by
    rw [Category.comp_id]; exact h
  have hdimU := supportDimension_le_of_openRestriction p pU j (𝟙 _) h' G r hdim
  -- The module on a fibre of `pU` is the pullback along the induced open immersion of fibres of
  -- the module on the corresponding fibre of `p`, the two composites to `Y` agreeing.
  have hres : ∀ s : Spec (CommRingCat.of R),
      fiberCycleRestrict p pU j h s r (familyAssociatedToModule p G r hdim s) =
        familyAssociatedToModule pU ((Scheme.Modules.pullback j).obj G) r hdimU s := by
    intro s
    have hfib : ∀ x : pU.fiber s,
        p.fiberι s (fiberRestrict p pU j h s x) = j (pU.fiberι s x) := by
      intro x
      have := congrArg (fun m : pU.fiber s ⟶ Y => m x) (fiberRestrict_fiberι p pU j h s)
      simpa only [Scheme.Hom.comp_apply] using this
    have e : (Scheme.Modules.pullback (pU.fiberι s)).obj ((Scheme.Modules.pullback j).obj G) ≅
        (Scheme.Modules.pullback (fiberRestrict p pU j h s)).obj
          ((Scheme.Modules.pullback (p.fiberι s)).obj G) :=
      (Scheme.Modules.pullbackComp (pU.fiberι s) j).app G ≪≫
        (Scheme.Modules.pullbackCongr (fiberRestrict_fiberι p pU j h s).symm).app G ≪≫
        ((Scheme.Modules.pullbackComp (fiberRestrict p pU j h s) (p.fiberι s)).app G).symm
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    rw [fiberCycleRestrict_apply, familyAssociatedToModule_apply_coeff,
      familyAssociatedToModule_apply_coeff]
    have hsupp : x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (pU.fiberι s)).obj
          ((Scheme.Modules.pullback j).obj G)) ↔
        fiberRestrict p pU j h s x ∈ SheafOfModules.supp
          ((Scheme.Modules.pullback (p.fiberι s)).obj G) := by
      rw [Stacks.Modules.supp_pullback (pU.fiberι s) ((Scheme.Modules.pullback j).obj G),
        Stacks.Modules.supp_pullback j G,
        Stacks.Modules.supp_pullback (p.fiberι s) G, Set.mem_preimage, Set.mem_preimage,
        Set.mem_preimage, hfib x]
    have hmult : sheafMultiplicity ((Scheme.Modules.pullback (pU.fiberι s)).obj
          ((Scheme.Modules.pullback j).obj G)) x =
        sheafMultiplicity ((Scheme.Modules.pullback (p.fiberι s)).obj G)
          (fiberRestrict p pU j h s x) := by
      rw [sheafMultiplicity_eq_of_iso e x,
        sheafMultiplicity_pullback_of_isOpenImmersion (fiberRestrict p pU j h s) _ x]
    have hdimx : relativeDimension
          (fieldDimensionFunction ((Spec (CommRingCat.of R)).residueField s))
          (pU.fiberToSpecResidueField s) x =
        relativeDimension
          (fieldDimensionFunction ((Spec (CommRingCat.of R)).residueField s))
          (p.fiberToSpecResidueField s) (fiberRestrict p pU j h s x) := by
      rw [← fiberRestrict_fiberToSpecResidueField p pU j h s]
      exact relativeDimension_comp_isOpenImmersion _ (fiberRestrict p pU j h s) _ x
    rw [hmult, ← hsupp, ← hdimx]
  refine fiberCycleRestrict_injective p pU j h r hcomp (IsLocalRing.closedPoint R) ?_
  rw [← specializationCycle_fiberCycleRestrict p pU j h r
      (familyAssociatedToModule p G r hdim (genericPoint (Spec (CommRingCat.of R)))),
    hres (genericPoint (Spec (CommRingCat.of R))), hres (IsLocalRing.closedPoint R)]
  exact specializationCycle_familyAssociatedToModule pU
    ((Scheme.Modules.pullback j).obj G) hflatU r
    (hdimU (genericPoint (Spec (CommRingCat.of R))))

/-! ### The specialization formula in dimensions where the module is flat -/

/-- The specialization formula over a discrete valuation ring for a module that is flat over the
base only in dimensions `≥ r`.

This strengthens Tag 0H4I, whose hypothesis is honest flatness of `G` over `R`, to the
hypothesis of Tag 0CWG that `G` be flat over the base in dimensions `≥ r`. The non-flat locus is
cut out of each fibre in dimension `< r`, so restricting to the open flat locus `U ⊆ Y` loses no
`r`-cycle, commutes with specialization, and lands in the situation of Tag 0H4I. -/
theorem specializationCycle_familyAssociatedToModule_of_isFlatOverInDimensionsGE
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p] (G : Y.Modules)
    [G.IsFiniteType] [G.IsQuasicoherent] (r : ℕ)
    (hG : AlgebraicGeometry.IsFlatOverInDimensionsGE p G r)
    (hdim : ∀ s : Spec (CommRingCat.of R), topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (p.fiberι s)).obj G)) ≤
        (r : WithBot ℕ∞)) :
    specializationCycle p r
        (familyAssociatedToModule p G r hdim (genericPoint (Spec (CommRingCat.of R)))) =
      familyAssociatedToModule p G r hdim (IsLocalRing.closedPoint R) := by
  -- The flat locus is open: `Spec R` is Noetherian, so `p` is locally of finite presentation,
  -- and `G` is coherent, hence of finite presentation.
  have : LocallyOfFinitePresentation p := inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType G
  have : G.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent G
  let U : Y.Opens := ⟨{y : Y | IsFlatOverAt p.toLRSHom.toShHom G y},
    AlgebraicGeometry.isOpen_setOf_flatOverAt p G⟩
  let j : U.toScheme ⟶ Y := U.ι
  have : LocallyOfFiniteType (j ≫ p) := inferInstance
  -- The fibrewise complement of the flat locus has dimension `< r`.
  have hcomp : ComplementFibreDimensionLT p (j ≫ p) j rfl r := by
    intro s x hx
    have hclosed : IsClosed
        {y : p.fiber s | ¬ IsFlatOverAt p.toLRSHom.toShHom G (p.fiberι s y)} :=
      (AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType p G s).isClosed_compl
    have hxT : x ∈ {y : p.fiber s | ¬ IsFlatOverAt p.toLRSHom.toShHom G (p.fiberι s y)} := by
      intro hflat
      rw [range_fiberRestrict p (j ≫ p) j rfl s] at hx
      exact hx ⟨⟨p.fiberι s x, hflat⟩, rfl⟩
    exact relativeDimension_lt_of_mem_of_topologicalKrullDim_lt
      (fieldChowSituation ((Spec (CommRingCat.of R)).residueField s)) (fun _ _ => rfl)
      (p.fiberToSpecResidueField s) hclosed (hG s) hxT
  -- On the flat locus the module is honestly flat over the base.
  have hflatU : AlgebraicGeometry.IsFlatOver (j ≫ p).toLRSHom.toShHom
      ((Scheme.Modules.pullback j).obj G) := by
    intro w
    rw [← AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso (j ≫ p).toLRSHom.toShHom
      ((Scheme.Modules.restrictFunctorIsoPullback j).app G) w]
    exact (AlgebraicGeometry.isFlatOverAt_restrict_iff j p G w).mpr w.2
  exact specializationCycle_familyAssociatedToModule_of_complementFibreDimensionLT p (j ≫ p) j
    rfl G r hdim hcomp hflatU

end Stacks.Chow

end
