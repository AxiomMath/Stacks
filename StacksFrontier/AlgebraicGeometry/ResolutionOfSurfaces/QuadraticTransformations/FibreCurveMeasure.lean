module

import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps

/-!
# The curves in the fibres, and the drop of their number under a blowup

The induction of [Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) runs on "the
number of curves in the fibres", for which the source says "some details omitted". This file
supplies that measure and proves its strict drop, which is the `descent` argument of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational`.

## Main definitions

* `Stacks.ResolutionOfSurfaces.fibreCurves` — the set of infinite irreducible closed subsets of
  the source which lie inside a single fibre of the morphism.
* `Stacks.ResolutionOfSurfaces.fibreCurveCount` — its cardinality, the measure itself.

## Main results

* `Stacks.ResolutionOfSurfaces.fibreCurves_mono` — the measure's set is monotone along a
  factorization: a curve inside a fibre of `ψ` is a curve inside a fibre of `ψ ≫ b`.
* `Stacks.ResolutionOfSurfaces.finite_fibreCurves` — the set is finite for a proper birational
  morphism between integral Noetherian schemes regular of dimension two.
* `Stacks.ResolutionOfSurfaces.not_finite_preimage_singleton_blowUpToBase_vanishingIdeal` — the
  fibre of the blowup at a closed point whose local ring has dimension two is infinite.
* `Stacks.ResolutionOfSurfaces.fibreCurveCount_lt_of_comp_eq_blowUpToBase_vanishingIdeal` — **the
  measure drops**: a factorization of a proper birational morphism through the blowup at a closed
  point of codimension two has strictly fewer curves in its fibres.

## The argument

Write `μ(g)` for the number of infinite irreducible closed subsets of the source contained in a
single fibre of `g`. Three facts give the drop at a factorization `ψ ≫ b = g` of `g` through the
blowup `b` of the chosen closed point `a`.

*Monotonicity is formal.* A curve inside the fibre of `ψ` over `z` is inside the fibre of `g`
over `b z`, so the set counted by `μ(ψ)` is a subset of the one counted by `μ(g)`. This is why
the measure counts curves in the fibres rather than curves in the exceptional set: no comparison
of the two isomorphism loci is needed.

*Finiteness is dimension two.* A curve inside a fibre of `g` lies inside the preimage `T` of the
complement of the maximal isomorphism open, because a fibre over a point of that open has one
point. `T` is a proper closed subset of the source, so by
`Stacks.ResolutionOfSurfaces.eq_of_not_finite_of_subset_of_ne_univ` any infinite irreducible
closed subset of `T` *is* one of the finitely many irreducible components of `T`: a strictly
smaller one would, with the component and the whole space, make a chain of four irreducible
closed subsets in a space of dimension two.

*Strictness is the exceptional curve.* The fibre of `b` over `a` is infinite — otherwise every
fibre of `b` would be finite, `b` would be an isomorphism, the centre would be an effective
Cartier divisor and the local ring at `a` would have dimension one by [Stacks, Tag 0BCN] rather
than the dimension two that
`Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open` gives it. Now
`ψ` is proper and dominant, hence surjective, so it carries the fibre of `g` over `a` onto the
fibre of `b` over `a`; one of the finitely many components of the former therefore has infinite
image, and that component is a curve in a fibre of `g` which is inside no fibre of `ψ` at all.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Curves in a space of dimension two -/

/-- **An infinite irreducible closed subset of a proper closed subset of an irreducible space of
dimension two is a component of it.** If it were strictly smaller than an irreducible closed set
`Z` which is not the whole space, then the closure of a non-generic point of it, it, `Z` and the
whole space would be a strictly increasing chain of four irreducible closed subsets, giving the
space dimension at least three. -/
public theorem eq_of_not_finite_of_subset_of_ne_univ {X : Type*} [TopologicalSpace X] [T0Space X]
    [QuasiSober X] [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 2) {C Z : Set X}
    (hCirr : IsIrreducible C) (hCcl : IsClosed C) (hCinf : ¬ C.Finite) (hZirr : IsIrreducible Z)
    (hZcl : IsClosed Z) (hZuniv : Z ≠ Set.univ) (hCZ : C ⊆ Z) :
    C = Z := by
  by_contra hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hCirr hCcl
  obtain ⟨p, hpC, hpξ⟩ : ∃ p ∈ C, p ≠ ξ := by
    by_contra! hcon
    exact hCinf ((Set.finite_singleton ξ).subset hcon)
  have hple : closure ({p} : Set X) ⊆ C :=
    hCcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hpC)
  have hpne : closure ({p} : Set X) ≠ C := fun h => hpξ (hξ.eq h).symm
  let P : IrreducibleCloseds X :=
    ⟨closure ({p} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let CC : IrreducibleCloseds X := ⟨C, hCirr, hCcl⟩
  let ZZ : IrreducibleCloseds X := ⟨Z, hZirr, hZcl⟩
  let TT : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hcoe : ∀ {V W : IrreducibleCloseds X}, V = W → (V : Set X) = (W : Set X) :=
    fun h => congrArg (fun V : IrreducibleCloseds X => (V : Set X)) h
  have h3 : ZZ < TT := lt_of_le_of_ne (Set.subset_univ Z) (fun h => hZuniv (hcoe h))
  have h2 : CC < ZZ := lt_of_le_of_ne hCZ (fun h => hne (hcoe h))
  have h1 : P < CC := lt_of_le_of_ne hple (fun h => hpne (hcoe h))
  let s : LTSeries (IrreducibleCloseds X) :=
    (((RelSeries.singleton _ TT).cons ZZ (by simpa using h3)).cons CC
      (by simpa using h2)).cons P (by simpa using h1)
  have hge : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    Order.LTSeries.length_le_krullDim s
  have hbad := hge.trans hdim
  norm_num at hbad

/-! ### The measure -/

/-- **The curves in the fibres of a morphism**: the infinite irreducible closed subsets of the
source contained in a single fibre. For a proper birational morphism between integral Noetherian
schemes regular of dimension two these are exactly the one-dimensional irreducible components of
the fibres, and there are finitely many of them
(`Stacks.ResolutionOfSurfaces.finite_fibreCurves`). -/
public def fibreCurves {A B : Scheme.{u}} (g : B ⟶ A) : Set (Set B) :=
  {C | IsIrreducible C ∧ IsClosed C ∧ ¬ C.Finite ∧ ∃ x : A, C ⊆ g ⁻¹' {x}}

/-- **The number of curves in the fibres of a morphism.** This is the measure on which the
induction of [Stacks, Tag 0C5R] runs. -/
public def fibreCurveCount (A B : Scheme.{u}) (g : B ⟶ A) : ℕ := (fibreCurves g).ncard

/-- **The curves in the fibres only grow along a factorization.** A curve inside the fibre of `ψ`
over `z` is inside the fibre of `ψ ≫ b` over `b z`. -/
public theorem fibreCurves_mono {A A' B : Scheme.{u}} {ψ : B ⟶ A'} {b : A' ⟶ A} {g : B ⟶ A}
    (hψ : ψ ≫ b = g) : fibreCurves ψ ⊆ fibreCurves g := by
  rintro C ⟨hirr, hcl, hinf, z, hz⟩
  refine ⟨hirr, hcl, hinf, b z, fun c hc => ?_⟩
  have hcz : ψ c = z := hz hc
  change g c = b z
  rw [← hψ, Scheme.Hom.comp_apply, hcz]

/-! ### Finiteness of the measure -/

/-- **A proper birational morphism between integral Noetherian schemes regular of dimension two
has finitely many curves in its fibres.** Such a curve lies over a point outside the maximal
isomorphism open, since a fibre over a point of that open is a single point; so it lies inside the
preimage `T` of the complement, which is a proper closed subset of the source because the morphism
is dominant and the open is nonempty. The source being Noetherian, `T` is a finite union of
irreducible closed subsets, and each curve inside `T`, being irreducible, lies inside one of them
and therefore equals it by
`Stacks.ResolutionOfSurfaces.eq_of_not_finite_of_subset_of_ne_univ`. -/
public theorem finite_fibreCurves {A B : Scheme.{u}} (hA : IsIntegralRegularSurface A)
    (hB : IsIntegralRegularSurface B) (g : B ⟶ A) (hp : IsProper g) (hb : IsBirational g) :
    (fibreCurves g).Finite := by
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hBint := hB.isIntegral
  have hBnoe := hB.isNoetherian
  have hAnormal : IsNormal A := isNormal_of_isRegular A hA.isRegular
  obtain ⟨U, hUiso, -, -, -, hUgen⟩ :=
    exists_finite_exceptional_set g hb (le_of_eq hA.topologicalKrullDim_eq)
  have hUne : ((U : Set A)).Nonempty := by
    refine ⟨genericPoint A, hUgen _ ?_⟩
    rw [genericPoints_eq_singleton]
    rfl
  set T : Set B := g ⁻¹' ((U : Set A)ᶜ)
  have hTcl : IsClosed T := (U.isOpen.isClosed_compl).preimage g.continuous
  have hTuniv : T ≠ Set.univ := by
    intro h
    obtain ⟨y, hyU⟩ := hUne
    have hrange : Set.range g ⊆ (U : Set A)ᶜ := by
      rintro - ⟨c, rfl⟩
      exact (h ▸ Set.mem_univ c : c ∈ T)
    have hcl : closure (Set.range g) ⊆ (U : Set A)ᶜ :=
      closure_minimal hrange U.isOpen.isClosed_compl
    rw [hb.isDominant.denseRange.closure_range] at hcl
    exact hcl (Set.mem_univ y) hyU
  obtain ⟨S, hSfin, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hTcl
  refine hSfin.subset ?_
  rintro C ⟨hCirr, hCcl, hCinf, x, hx⟩
  have hxU : x ∉ U := fun hmem =>
    hCinf ((finite_fiber_of_isIso_restrict g U hUiso hmem).subset hx)
  have hCT : C ⊆ T := by
    intro c hc
    have : g c = x := hx hc
    exact (show g c ∈ (U : Set A)ᶜ from this ▸ hxU)
  lift S to Finset (Set B) using hSfin
  obtain ⟨Z, hZS, hCZ⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hCirr S (fun Z hZ => hScl Z hZ)
      (hTS ▸ hCT)
  have hZT : Z ⊆ T := by
    rw [hTS]
    exact Set.subset_sUnion_of_mem hZS
  exact (eq_of_not_finite_of_subset_of_ne_univ (le_of_eq hB.topologicalKrullDim_eq) hCirr hCcl
    hCinf (hSirr Z hZS) (hScl Z hZS) (fun h => hTuniv (Set.univ_subset_iff.mp (h ▸ hZT))) hCZ) ▸
    hZS

/-! ### The fibre of the blowup at a point of codimension two -/

/-- **The blowup at a closed point whose local ring has dimension two has an infinite fibre over
that point.** Were the fibre finite, every fibre of the blowup would be finite — the blowup is an
isomorphism away from its centre — so the blowup would be an isomorphism, its centre would then be
an effective Cartier divisor, and part (2) of [Stacks, Tag 0BCN] would give the local ring at the
point dimension one. -/
public theorem not_finite_preimage_singleton_blowUpToBase_vanishingIdeal {A : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsIntegral A] [IsNormal A]
    (hdim : topologicalKrullDim A = 2) {a : A} (ha : IsClosed ({a} : Set A))
    (hstalk : ringKrullDim (A.presheaf.stalk a) = 2) :
    ¬ ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) ⁻¹' {a} :
      Set (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))).Finite := by
  intro hfin
  set M : A.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A) with hM
  have hMbot : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot hdim a ha
  have hBint : AlgebraicGeometry.IsIntegral (blowUp M) := isIntegral_blowUp M hMbot
  have hLN : IsLocallyNoetherian A := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have hbir : IsBirational (blowUpToBase M) := isBirational_blowUpToBase M hMbot
  have hsupp : (M.support : Set A) = {a} := by
    rw [hM, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hall : ∀ x : A, ((blowUpToBase M) ⁻¹' {x}).Finite := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      exact hfin
    · refine finite_fiber_of_isIso_restrict (blowUpToBase M) M.support.compl inferInstance ?_
      change x ∈ ((M.support : Set A)ᶜ)
      rw [hsupp]
      simpa using hxa
  have hiso : IsIso (blowUpToBase M) := isIso_of_finite_fibres (blowUpToBase M) hbir hall
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor M :=
    isEffectiveCartierDivisor_of_isIso_blowUpToBase M
  have hmem : a ∈ Set.range M.subschemeι := by
    rw [M.range_subschemeι, hsupp]
    rfl
  obtain ⟨ξ, hξ⟩ := hmem
  have huniv : ({ξ} : Set M.subscheme) = Set.univ := by
    refine Set.eq_univ_of_forall fun ζ =>
      Set.mem_singleton_iff.mpr (M.subschemeι.isClosedEmbedding.injective ?_)
    have h1 : M.subschemeι ζ ∈ Set.range M.subschemeι := ⟨ζ, rfl⟩
    rw [M.range_subschemeι, hsupp] at h1
    rw [hξ]
    simpa using h1
  have hcomp : ∃ Z : irreducibleComponents M.subscheme, IsGenericPoint ξ (Z : Set M.subscheme) := by
    refine ⟨⟨Set.univ, huniv ▸ isIrreducible_singleton, fun s hs _ => Set.subset_univ s⟩, ?_⟩
    change closure ({ξ} : Set M.subscheme) = Set.univ
    rw [huniv, closure_univ]
  have h1 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor M hcart ξ hcomp
  rw [hξ, hstalk] at h1
  norm_num at h1

/-! ### The drop of the measure -/

/-- **The measure drops at a factorization through the blowup at a closed point of codimension
two.** This is the `descent` argument of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational`: if `g : B ⟶ A` is a
proper birational morphism between integral Noetherian schemes regular of dimension two, `a` is a
closed point whose local ring has dimension two — which
`Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open` supplies for a
closed point outside the maximal open over which `g` is an isomorphism — and the proper birational
`ψ` factors `g` through the blowup of `A` at `a`, then `ψ` has strictly fewer curves in its fibres
than `g`.

That the blowup is again an integral Noetherian scheme regular of dimension two — the
globalization of [Stacks, Tag 0AGR] — is the hypothesis `hA'`;
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal` of
`FactorizationBirationalMapsDimTwo.lean` discharges it. It is an argument rather than an import
because this file reaches the private lemmas of `DominateByNormalizedBlowUps/Basic.lean` through
`import all`, and that module also arriving on a `public import` path — which importing
`FactorizationBirationalMapsDimTwo.lean` would do — makes those private names invisible here. -/
public theorem fibreCurveCount_lt_of_comp_eq_blowUpToBase_vanishingIdeal {A B : Scheme.{u}}
    (g : B ⟶ A) (hA : IsIntegralRegularSurface A) (hB : IsIntegralRegularSurface B)
    (hp : IsProper g) (hb : IsBirational g) {a : A} (ha : IsClosed ({a} : Set A))
    (hstalk : ringKrullDim (A.presheaf.stalk a) = 2)
    (hA' : IsIntegralRegularSurface
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    (ψ : B ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))
    (hpψ : IsProper ψ) (hbψ : IsBirational ψ)
    (hψ : ψ ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)) = g) :
    fibreCurveCount (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) B ψ <
      fibreCurveCount A B g := by
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hBint := hB.isIntegral
  have hBnoe := hB.isNoetherian
  have hAnormal : IsNormal A := isNormal_of_isRegular A hA.isRegular
  -- the instances that make `ψ` surjective (used in `himg`)
  have hA'int := hA'.isIntegral
  have hA'noe := hA'.isNoetherian
  have hLN : IsLocallyNoetherian A := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have hdomψ := hbψ.isDominant
  -- the fibre of the blowup over `a` is infinite
  have hfib :=
    not_finite_preimage_singleton_blowUpToBase_vanishingIdeal hA.topologicalKrullDim_eq ha hstalk
  -- `ψ` carries the fibre of `g` over `a` onto it
  have hpre : (g ⁻¹' {a} : Set B) = ψ ⁻¹'
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) ⁻¹' {a}) := by
    ext c
    simp [← hψ]
  have himg : ψ '' (g ⁻¹' {a}) =
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) ⁻¹' {a} :
        Set (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))) := by
    rw [hpre, Set.image_preimage_eq _ ψ.surjective]
  -- decompose the fibre of `g` over `a`
  obtain ⟨S, hSfin, hScl, hSirr, hSU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (ha.preimage g.continuous)
  obtain ⟨C, hCS, hCimg⟩ : ∃ C ∈ S, ¬ (ψ '' C).Finite := by
    by_contra! hcon
    refine hfib ?_
    rw [← himg, hSU, Set.image_sUnion]
    exact (hSfin.image _).sUnion (Set.forall_mem_image.2 hcon)
  have hCsub : C ⊆ g ⁻¹' {a} := by
    rw [hSU]
    exact Set.subset_sUnion_of_mem hCS
  have hCg : C ∈ fibreCurves g :=
    ⟨hSirr C hCS, hScl C hCS, fun h => hCimg (h.image _), a, hCsub⟩
  have hCψ : C ∉ fibreCurves ψ := by
    rintro ⟨-, -, -, z, hz⟩
    exact hCimg ((Set.finite_singleton z).subset (Set.image_subset_iff.mpr hz))
  exact Set.ncard_lt_ncard ⟨fibreCurves_mono hψ, fun h => hCψ (h hCg)⟩
    (finite_fibreCurves hA hB g hp hb)

end Stacks.ResolutionOfSurfaces

end
