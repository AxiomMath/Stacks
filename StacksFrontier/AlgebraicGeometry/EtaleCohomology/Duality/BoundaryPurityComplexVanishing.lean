module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinVanishingOfPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveFirstBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition

/-!
# `H²(Rf̄_*(R j_*(j⁻¹ H)))` vanishes at the points under an étale boundary divisor

Let `f̄ : X̄ ⟶ S` be proper and smooth of relative dimension one with geometrically irreducible
fibres, over `S` smooth over a field `k`, `i : Z ⟶ X̄` a closed immersion with `Z ⟶ S` finite
étale, `j : U ⟶ X̄` the open complement, `N` invertible in `k` and `H` a locally constant sheaf of
finite type of `ℤ/N`-modules on `X̄`. At the geometric point over a point `y ∈ S` lying under `Z`,
the inverse image of `H²(Rf̄_!(R j_*(j⁻¹ H)))` (`f̄` being its own compactification) vanishes
(`Stacks.EtaleCohomology.isZero_inverseImage_homology_two_derivedLowerShriek_purityComplex`):

1. by proper base change for `Rf̄_!` ([Stacks, Tag 0F7L]) it is `H²` of `Rf̄'_!` on the geometric
   fibre `X̄_ȳ`, of the inverse image of `R j_*(j⁻¹ H)`;
2. that inverse image is `R j'_*(j'⁻¹ u⁻¹ H)` (relative purity `(P0)`, `(P2)`, `(BC1)` on `X̄` and
   on `X̄_ȳ`, `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_single_restriction`);
3. `X̄_ȳ` is an irreducible curve over the algebraically closed `κ(y)‾` which meets `Z`, so the
   complement of `Z` in it is an affine curve and `H²_c(X̄_ȳ, R j'_* F) = 0`
   (`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed`).

This is the vanishing behind the surjectivity, at the points under `Z`, of the Gysin map
`R⁰f̄_*(R¹ j_* Λ) ⟶ R² f̄_* Λ` (`Stacks.EtaleCohomology.lowerShriekGysin`), in the proof of the
duality along the boundary divisor of a relative curve, part of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Implementation notes

The statement is made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.derivedLowerShriek` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`H²(Rf̄_!(R j_*(j⁻¹ H)))` vanishes at the geometric point over a point under `Z`**, for the
complement `j` of an étale divisor `Z` of a proper smooth relative curve `f̄` with geometrically
irreducible fibres, over a base smooth over a field in which `N` is invertible, and `H` locally
constant of finite type: by proper base change it is `H²_c` of the complement of `Z` in the
geometric fibre, an affine curve. -/
theorem isZero_inverseImage_homology_two_derivedLowerShriek_purityComplex (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {S Xbar Z U : Scheme.{u}} (pS : S ⟶ Spec (.of k))
    [Smooth pS] (fbar : Xbar ⟶ S) [SmoothOfRelativeDimension 1 fbar] [IsProper fbar]
    [GeometricallyIrreducible fbar] (i : Z ⟶ Xbar) [IsClosedImmersion i] [IsFinite (i ≫ fbar)]
    [Etale (i ≫ fbar)] (j : U ⟶ Xbar) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (H : EtaleModules.{u, 0} (ZMod N) Xbar)
    (hH : lccModules Xbar N H) (y : S) (hy : y ∈ Set.range (i ≫ fbar).base) :
    IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) (GeometricPoint.ofPoint S y).hom).obj
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((derivedLowerShriek.{u, 0} fbar (CompactificationOf.ofProper fbar) (ZMod N)).obj
          ((purityComplex (ZMod N) j).obj H)))) := by
  let jg := CompactificationOf.ofProper fbar
  let K := (purityComplex (ZMod N) j).obj H
  let s := (GeometricPoint.ofPoint S y).hom
  let Ω := (GeometricPoint.ofPoint S y).residueField
  have hsq : IsPullback (pullback.fst fbar s) (pullback.snd fbar s) fbar s :=
    IsPullback.of_hasPullback fbar s
  have := isIso_derivedLowerShriekBaseChange_app (ZMod N) hsq jg K
    (isTorsionPlus_of_nsmul_id_eq_zero K N (NeZero.pos N) (nsmul_id_purityComplex_zmod N j H))
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso (ZMod N) s
    ((derivedLowerShriek.{u, 0} fbar jg (ZMod N)).obj K) 2
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    (asIso ((derivedLowerShriekBaseChange.{u, 0} (ZMod N) hsq jg).app K)).symm ≪≫ e).symm
  -- the geometric fibre over `y`
  let u' := pullback.fst fbar s
  let g' := pullback.snd fbar s
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 g' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hsq inferInstance
  let U' : Scheme.{u} := pullback fbar s
  let j' := pullback.snd j u'
  let u₀ := pullback.fst j u'
  have sq : IsPullback u₀ j' j u' := IsPullback.of_hasPullback j u'
  let i' := pullback.snd i u'
  have sqi : IsPullback (pullback.fst i u') i' i u' := IsPullback.of_hasPullback i u'
  have sqig : IsPullback (pullback.fst i u') (i' ≫ g') (i ≫ fbar) s := sqi.paste_vert hsq
  have : IsFinite (i' ≫ g') := MorphismProperty.of_isPullback sqig inferInstance
  have : Etale (i' ≫ g') := MorphismProperty.of_isPullback sqig inferInstance
  have hj' : Set.range j'.base = (Set.range i'.base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hj, Set.preimage_compl]
  have hNΩ : IsUnit ((N : ℕ) : Ω) := by
    have hu := Purity.isUnit_natCast_globalSections_of_over (k := k) (ℓ := N) (s ≫ pS) hN
    simpa using hu.map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  have hH' := lccModules_etaleModuleInverseImage N u' H hH
  have h0' := Purity.purityUnitIso_of_affineLine Ω N hNΩ (Purity.affineLineConstantUnitIso Ω)
    (𝟙 (Spec (.of Ω))) g' i' j' hj' _ hH'
  have h2' := Purity.purityHigherDirectImageVanishing_of_affineLine Ω N hNΩ
    (Purity.affineLineTorsionVanishing Ω) (𝟙 (Spec (.of Ω))) g' i' j' hj' _ hH'
  have hP0 := Purity.purityUnitIso_of_affineLine k N hN (Purity.affineLineConstantUnitIso k) pS
    fbar i j hj H hH
  have hP2 := Purity.purityHigherDirectImageVanishing_of_affineLine k N hN
    (Purity.affineLineTorsionVanishing k) pS fbar i j hj H hH
  have hBC := Purity.purityFirstBaseChangeIso_of_relativeCurve k N hN pS fbar i j hj
    (𝟙 (Spec (.of Ω))) s u' g' hsq j' u₀ sq H hH
  have hβ := isIso_etaleModuleDerivedBaseChange_app_single_restriction (ZMod N) j j' u' u₀ sq H
    hP0 h0' hBC hP2 h2'
  -- `H²_c` of `R j'_*` on the fibre
  have hdim : topologicalKrullDim U' ≤ 1 := by
    rcases isEmpty_or_nonempty U' with h | h
    · have : IsEmpty (TopologicalSpace.IrreducibleCloseds U') :=
        ⟨fun Z => h.elim Z.isIrreducible.nonempty.some⟩
      change Order.krullDim (TopologicalSpace.IrreducibleCloseds U') ≤ 1
      rw [Order.krullDim_eq_bot]; exact bot_le
    · rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 g']; rfl
  have hfib' : ∀ C ∈ irreducibleComponents U', (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
      (C ∩ Set.range i'.base).Nonempty := by
    intro C hC _
    have : IrreducibleSpace U' :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := g')
    have hCU : C = Set.univ := by
      rw [irreducibleComponents_eq_singleton] at hC
      exact hC
    obtain ⟨z, hz⟩ := hy
    obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := fbar) (g := s)
      (i.base z) (default : Spec (.of Ω))
        ((show fbar.base (i.base z) = y from hz).trans (GeometricPoint.ofPoint_liesOver S y).symm)
    refine ⟨p, hCU ▸ Set.mem_univ p, ?_⟩
    rw [Scheme.Pullback.range_snd]
    exact ⟨z, hp₁.symm⟩
  have hV := isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed Ω g'
    (jg.baseChange hsq) i' j' hj' hdim hfib' N
    ((etaleModuleInverseImage.{u, 0} (ZMod N) u₀).obj
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))
  exact hV.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriek.{u, 0} g' (jg.baseChange hsq) (ZMod N)).mapIso
      (asIso ((etaleModuleDerivedBaseChange.{u, 0} (ZMod N) j j' u' u₀ sq.w.symm).app _) ≪≫
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j').mapIso
          ((etaleModuleInverseImage.{u, 0} (ZMod N) u₀).mapDerivedCategoryPlusObjSingleIso _))))

/-- **`H²(Rf̄_*(R j_*(j⁻¹ H)))` vanishes at the geometric point over a point under `Z`**: the same
statement for `Rf̄_*`, which is `Rf̄_!` through the trivial compactification of the proper `f̄`
(`Stacks.EtaleCohomology.derivedLowerShriekOfProperIso`). -/
theorem isZero_inverseImage_homology_two_derivedDirectImage_purityComplex (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {S Xbar Z U : Scheme.{u}} (pS : S ⟶ Spec (.of k))
    [Smooth pS] (fbar : Xbar ⟶ S) [SmoothOfRelativeDimension 1 fbar] [IsProper fbar]
    [GeometricallyIrreducible fbar] (i : Z ⟶ Xbar) [IsClosedImmersion i] [IsFinite (i ≫ fbar)]
    [Etale (i ≫ fbar)] (j : U ⟶ Xbar) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (H : EtaleModules.{u, 0} (ZMod N) Xbar)
    (hH : lccModules Xbar N H) (y : S) (hy : y ∈ Set.range (i ≫ fbar).base) :
    IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) (GeometricPoint.ofPoint S y).hom).obj
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar).obj
          ((purityComplex (ZMod N) j).obj H)))) :=
  (isZero_inverseImage_homology_two_derivedLowerShriek_purityComplex k N hN pS fbar i j hj H hH
    y hy).of_iso ((etaleModuleInverseImage.{u, 0} (ZMod N) (GeometricPoint.ofPoint S y).hom).mapIso
      ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
        ((derivedLowerShriekOfProperIso (ZMod N) fbar).app _))).symm

end Stacks.EtaleCohomology

end
