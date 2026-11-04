module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QA

/-!
# The bounds of [Stacks, Tag 07QA] with the annihilation read off the tower

`SmallSite/CrisCohomologyBound07QA.lean` states the kernel and the cokernel bounds of
[Stacks, Tag 07QA] on the crystalline cohomology groups themselves, each taking
`...SmallSite.Annihilation07Q9` for a single number `q`.  The source does not produce that `q` in
one step: it writes the iterated `α_p`-cover as a tower `X' = X_n ⟶ ⋯ ⟶ X_0 = X` of `α_p`-covers,
annihilates the cone of each stage by `p`, and multiplies.  **This file states the two bounds with
the annihilation in that form** — one hypothesis per stage, for `p`, and the exponent `p ^ n`
assembled by `...SmallSite.annihilation07Q9_chainComp`.

## What the factorisation hypothesis is, and what it is not

Both theorems take, besides the per-stage annihilation, an equation

`derivedZariskiComparison ⋯ F = e₁.hom ≫ chainComp Y α n ≫ e₂.hom`

identifying the comparison map of [Stacks, Tag 07Q9] for the whole cover with the composite of
the stages' comparison maps, up to isomorphisms at the two ends.  That is the **composition
functoriality of `...SmallSite.derivedZariskiComparison`**, and it is taken as an argument here
only so that this file does not depend on where it is proved: it **is** proved, with no
hypotheses, as `...SmallSite.derivedZariskiComparison_comp'` of
`SmallSite/DerivedCrisZariskiComposition.lean`.  The underived form is
`...SmallSite.zariskiComparison_comp'` of `SmallSite/CrisZariskiCellCompositionProof.lean`,
whose coherence input `...SmallSite.CrisZariskiCellComp` is the theorem
`...SmallSite.crisZariskiCellComp` there.

It is not the mathematics of [Stacks, Tag 07Q9].  That mathematics is the
*per-stage* annihilation — [Stacks, Proposition 60.21.3, Tag 07LG] together with
[Stacks, Lemma 60.25.1, Tag 07Q7] at `a = p` for the extension of [Stacks, Tag 07N1] — and it is
exactly what the hypothesis `hα` below asks for, one stage at a time.  The factorisation is
assembly: four functors composed two ways.  Isolating the two makes it visible which input of
the tower route is a proposition and which is plumbing.

The isomorphisms `e₁` and `e₂` are what make the hypothesis usable: a composition functoriality
presents the comparison of a composite only up to the composition isomorphisms of the Zariski
pushforwards and of the crystalline inverse images, as `...SmallSite.zariskiComparison_comp`
does, and `...SmallSite.annihilation07Q9_isIso_comp` and
`...SmallSite.annihilation07Q9_comp_isIso` absorb them at no cost.

## Main results

* `pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA_of_tower` — **the kernel half of
  [Stacks, Tag 07QA] from the tower**: if each of the `n` stages annihilates its cone's cohomology
  sheaves by `p`, the kernel of `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` is annihilated by
  `(p ^ n) ^ {i + 1}`.
* `exists_crisCohomologyMap_eq_pow_smul_07QA_of_tower` — **the cokernel half from the tower**,
  with the monomorphism hypothesis in the exact form of `...SmallSite.CrisUnitMono`.

## No tag is placed

No tag attribute is placed here.  Both theorems take the per-stage annihilation and the
factorisation of the comparison map as arguments, and the cokernel half the monomorphism of
`u_{X/S, *}` of the crystalline unit, so that they apply to any presentation of the cover as a
tower.  [Stacks, Tag 07QA] itself is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, which takes the annihilation from [Stacks, Tag 07Q9]
(`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`, proved over chain opens rather than
stage by stage) and the monomorphism from
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.

What the file records is that the tower route is also available: the propagation from the
per-stage annihilation to the composite's is a theorem, and so is the factorisation named above
(`...SmallSite.derivedZariskiComparison_comp'`).

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.1, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Tower

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

omit [HasDerivedCategory AddCommGrpCat] in
/-- **The annihilation of [Stacks, Tag 07Q9] for the whole cover, from its stages.**  If the
comparison map `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` factors, up to isomorphisms at the two
ends, as the composite of `n` maps each satisfying `...SmallSite.Annihilation07Q9` for `p`, then
it satisfies it for `p ^ n`.

The exponent is the source's `p ^ n = q`, and over an affine base
`AlgebraicGeometry.hasConstantDegree_alphaPTowerComp` of
`Crystalline/AlphaPCoverDegree.lean` computes that same `p ^ n` as the constant degree of a tower
of `n` stages.

Nothing here is the mathematics of [Stacks, Tag 07Q9]: the per-stage hypothesis `hα` is, and the
factorisation `hfact` is the composition functoriality of the comparison map, proved in derived
form as `...SmallSite.derivedZariskiComparison_comp'`. -/
theorem annihilation07Q9_derivedZariskiComparison_of_tower (p n : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (Y : ℕ → DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    (α : ∀ j : ℕ, Y j ⟶ Y (j + 1)) (hα : ∀ j : ℕ, Annihilation07Q9 S' p (α j))
    (e₁ : (derivedZariskiDirectImage S').obj F ≅ Y 0)
    (e₂ : Y n ≅ (derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))
    (hfact : derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F =
      e₁.hom ≫ Stacks.Triangulated.chainComp Y α n ≫ e₂.hom) :
    Annihilation07Q9 S' (p ^ n)
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F) := by
  rw [hfact]
  exact annihilation07Q9_isIso_comp S' (p ^ n) e₁.hom _
    (annihilation07Q9_comp_isIso S' (p ^ n) _ e₂.hom
      (annihilation07Q9_chainComp S' p Y α hα n))

/-- **The kernel half of [Stacks, Tag 07QA] with the annihilation read off the tower.**  For a
cover presented as a tower of `n` stages, each of which annihilates the cohomology sheaves of its
cone by `p`, the kernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

is annihilated by `(p ^ n) ^ {i + 1}` — the source's `q ^ {i + 1}` with `q = p ^ n` the degree of
the composite cover.

This is `...SmallSite.pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA` with its single
hypothesis supplied by `annihilation07Q9_derivedZariskiComparison_of_tower`.  No tag attribute
is placed on this lemma: `hα` is the per-stage annihilation and `hfact` the composition
functoriality, the latter proved as `...SmallSite.derivedZariskiComparison_comp'`.  [Stacks,
Tag 07QA] is `...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`.
-/
theorem pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA_of_tower (p n i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (Y : ℕ → DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    (α : ∀ j : ℕ, Y j ⟶ Y (j + 1)) (hα : ∀ j : ℕ, Annihilation07Q9 S' p (α j))
    (e₁ : (derivedZariskiDirectImage S').obj F ≅ Y 0)
    (e₂ : Y n ≅ (derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))
    (hfact : derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F =
      e₁.hom ≫ Stacks.Triangulated.chainComp Y α n ≫ e₂.hom)
    (x : (cohomologyFunctor S' i).obj F)
    (hx : crisCohomologyMap S S' fS fX hf F i x = 0) :
    (((p ^ n : ℕ) : ℤ) ^ (i + 1)) • x = 0 :=
  pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA S S' fS fX hf (p ^ n) i F
    (annihilation07Q9_derivedZariskiComparison_of_tower S S' fS fX hf p n F Y α hα e₁ e₂ hfact)
    x hx

/-- **The cokernel half of [Stacks, Tag 07QA] with the annihilation read off the tower.**  For a
cover presented as a tower of `n` stages, each annihilating the cohomology sheaves of its cone by
`p`, and given that `u_{X/S, *}` of the crystalline unit `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a
monomorphism, `(p ^ n) ^ {i + 1}` times any class in `H^i(Cris(X'/S), ℱ')` is in the image of
`f^*`.

The monomorphism is in the exact form of `SmallSite/CrisUnitMono.lean`, which
`...SmallSite.mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` shows is
equivalent to what the bound consumes rather than merely sufficient for it; the ring-level input
to it is the split injection `Crystalline.PthRootExtension.injective_completedToPrimeRing`, and
the passage from that to the site, for a crystal in quasi-coherent modules, is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.  No tag
attribute is placed on this lemma. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA_of_tower (p n i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (Y : ℕ → DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    (α : ∀ j : ℕ, Y j ⟶ Y (j + 1)) (hα : ∀ j : ℕ, Annihilation07Q9 S' p (α j))
    (e₁ : (derivedZariskiDirectImage S').obj F ≅ Y 0)
    (e₂ : Y n ≅ (derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))
    (hfact : derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F =
      e₁.hom ≫ Stacks.Triangulated.chainComp Y α n ≫ e₂.hom)
    (hmono : Mono ((zariskiDirectImage S').map (crisUnit S S' fS fX hf F)))
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, (((p ^ n : ℕ) : ℤ) ^ (i + 1)) • y = crisCohomologyMap S S' fS fX hf F i x :=
  exists_crisCohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit S S' fS fX hf (p ^ n) i F
    (annihilation07Q9_derivedZariskiComparison_of_tower S S' fS fX hf p n F Y α hα e₁ e₂ hfact)
    hmono y

end Tower

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
