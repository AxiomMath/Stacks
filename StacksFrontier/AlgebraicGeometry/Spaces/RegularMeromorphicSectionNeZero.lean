module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRatio

/-!
# Regular meromorphic sections of an invertible module on an integral space are the nonzero ones

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `ℒ` be an
invertible `𝒪_X`-module. A meromorphic section of `ℒ` is regular exactly when it is nonzero.
This is the identification the source makes at the start of its construction of
`Pic(X) → Cl(X)` (Spaces over Fields, Section 0EPP): by Stacks 0ENA a regular meromorphic
section is the same thing as a nonzero element of `ℒ_η`. It is what makes the statements of
Stacks 0EPU and 0EQE, which speak of a *nonzero* meromorphic section, the statements about
*regular* ones that the order of vanishing of Stacks 0EPR is defined for.

The proof goes through the trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ: every meromorphic
section is `a · t` for the image `t` of the unit section, which is regular, and a global
meromorphic function `a`; the global meromorphic functions form the function field (Stacks
0ENA), so `a ≠ 0` is invertible, and multiplication by `a · t` on any étale chart is
multiplication by the unit `a` followed by multiplication by `t`.

## Main results

* `AlgebraicGeometry.Space.isRegularMeromorphicSection_iff_ne_zero`.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **A meromorphic section of an invertible module on a locally Noetherian integral algebraic
space is regular exactly when it is nonzero.** A regular section is nonzero because the ring of
global meromorphic functions is a field, hence nontrivial. Conversely a nonzero section is
`a · t` for the image `t` of the unit section under the trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks
0EPQ, with `a` a nonzero, hence invertible, global meromorphic function; multiplication by
`a · t` on an étale chart is multiplication by the unit `a` followed by the injective
multiplication by `t`. -/
theorem isRegularMeromorphicSection_iff_ne_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX L s ↔ s ≠ 0 := by
  -- the three conditions of Stacks 0ENA on such an `X`
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hmono := IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
    ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩
  obtain ⟨e⟩ := nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints B S hS hX
    hwa hfin hmono L hL
  obtain ⟨eR, -⟩ := exists_ringEquiv_rationalFunctions_meromorphicFunction
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) hwa hfin hmono
  -- `Γ(X, 𝒦_X) = R(X)` is a field
  have hfieldK : IsField (↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) :=
    MulEquiv.isField (isField_rationalFunctions B S hS hX hInt) eR.symm.toMulEquiv
  refine ⟨fun hs hs0 => ?_, fun hs0 => ?_⟩
  · have : Nontrivial ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)) :=
      ⟨hfieldK.exists_pair_ne⟩
    refine one_ne_zero (show (1 : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) = 0
      from Subtype.ext (funext fun W => hs W.unop ?_))
    change (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj W) • s.eval W =
      (0 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj W) • s.eval W
    rw [hs0]
    simp
  · -- `s = a · t` for the image `t` of the unit section
    have hlin : ∀ (a : ↥(RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))
        (x : (meromorphicUnitModule B S hS X hX).sections),
        SheafOfModules.sectionsMap e.hom (a • x) = a • SheafOfModules.sectionsMap e.hom x :=
      fun a x => ((Stacks.Cohomology.SiteModules.globalSectionsFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O)).map e.hom).hom.map_smul a x
    have hround : SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv s) = s :=
      Subtype.ext (funext fun V =>
        congrArg (fun φ : meromorphicSectionSheaf.{u, u} B S hS X hX L ⟶
            meromorphicSectionSheaf.{u, u} B S hS X hX L =>
          PresheafOfModules.Hom.app φ.val V (s.eval V)) e.inv_hom_id)
    obtain ⟨a, ha, -⟩ := existsUnique_smul_meromorphicUnitSection B S hS hX
      (SheafOfModules.sectionsMap e.inv s)
    let t := SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS X hX)
    have hsa : s = a • t := by rw [← hlin, ha, hround]
    have ha0 : a ≠ 0 := fun h => hs0 (by rw [hsa, h, zero_smul])
    obtain ⟨z, hz⟩ := hfieldK.mul_inv_cancel ha0
    have ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t := by
      intro V r₁ r₂ hr
      refine injective_smul_meromorphicUnitSection B S hS X hX V ?_
      refine (ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O) (op V)).map e.hom)).injective ?_
      have hlinV : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
          (PresheafOfModules.Hom.app e.hom.val (op V)).hom
              (r • (meromorphicUnitSection B S hS X hX).eval (op V)) =
            r • t.eval (op V) :=
        fun r => (PresheafOfModules.Hom.app e.hom.val (op V)).hom.map_smul r _
      exact (hlinV r₁).trans (hr.trans (hlinV r₂).symm)
    rw [hsa]
    intro V r₁ r₂ hr
    have hr' : (r₁ * a.1 (op V)) • t.eval (op V) = (r₂ * a.1 (op V)) • t.eval (op V) := by
      have : (a • t).eval (op V) = a.1 (op V) • t.eval (op V) := rfl
      rw [mul_smul, mul_smul, ← this]
      exact hr
    have hzV : a.1 (op V) * z.1 (op V) = 1 := congrFun (congrArg Subtype.val hz) (op V)
    exact (IsUnit.of_mul_eq_one _ hzV).mul_left_inj.1 (ht V hr')

end AlgebraicGeometry.Space

end
