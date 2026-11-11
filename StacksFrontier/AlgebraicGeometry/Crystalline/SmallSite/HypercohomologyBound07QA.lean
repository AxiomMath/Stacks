module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.UnderivedLerayCoherence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiHypercohomology

/-!
# The bounds of [Stacks, Tag 07QA] on Zariski hypercohomology groups

[Stacks, Tag 07QA] bounds the kernel and the cokernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

by `q^{i + 1}`.  `SmallSite/AlphaPCoverTriangle.lean` proves the two bounds as statements about an
abstract distinguished triangle in `D(Ab(X_Zar))` and about *morphisms of the derived category*
out of an object concentrated in degrees `≤ i`
(`...SmallSite.pow_smul_eq_zero_of_kernel_07QA` and
`...SmallSite.exists_comp_mor₁_eq_pow_smul_07QA_of_mono`).  This file reads those two bounds as
statements about the kernel and the cokernel of a map of cohomology **groups**, namely of the map
induced on `H^i(X_Zar, -)` by the comparison map

`Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'`

of [Stacks, Tag 07Q9].

## What this file supplies, and what it still carries

Three of the four inputs the bounds need are now declarations of this library, and this file uses
them rather than taking them:

* the commutation of the square of topoi, `...SmallSite.crisZariskiSquare`, so that the comparison
  map `...SmallSite.derivedZariskiComparison` is formed with no datum;
* the corepresentation `H^i(RΓ(X_Zar, K)) ≃+ Hom(ℤ_X[0]⟦-i⟧, K)` of Zariski hypercohomology
  together with **its naturality in `K`**,
  `...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` and
  `...derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality` of
  `SmallSite/ZariskiHypercohomology.lean`, which is what turns a statement about morphisms of
  `D(Ab(X_Zar))` into a statement about elements of a cohomology group;
* the concentration of both terms of the triangle in degrees `≥ 0`, proved here as
  `isGE_derivedZariskiDirectImage_obj` and `isGE_derivedZariskiPushforward_obj` from
  `CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`.  This is what buys the source's
  exponent `q^{i + 1}` for the kernel with no further hypothesis.

The fourth is taken as an input: `...SmallSite.Annihilation07Q9`, the conclusion of
[Stacks, Tag 07Q9] that the third term of the triangle has cohomology sheaves annihilated by `q`,
so that the bounds hold for any annihilator.  For a crystal in quasi-coherent modules it is
[Stacks, Tag 07Q9] itself, `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
`SmallSite/AlphaPCover07Q9Main.lean`, whose mathematical content is [Stacks, Proposition 07LG],
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.

The cokernel half takes one further hypothesis, `hmono`, in the form the bound consumes it: that
`ℋ^0` of the comparison map is a monomorphism.  The module documentation of
`SmallSite/AlphaPCoverTriangle.lean` explains why that is the source's own observation rather than
a weakening — `ℋ^{-1}(E)` is its kernel, and the source's exponent `q^{i + 1}` rather than
`q^{i + 2}` for the cokernel holds exactly when it vanishes.  The ring-level input to it, the
splitness of `D ⟶ D'` of [Stacks, Tag 07N1] for a single `p`-th root extension, is
`Crystalline.PthRootExtension.injective_completedToPrimeRing`; the passage from that to the
monomorphism on the site, for a crystal in quasi-coherent modules, is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover` of
`SmallSite/ModuleUnitMonoRings07QA.lean`.

## Main results

* `isGE_derivedZariskiDirectImage_obj` and `isGE_derivedZariskiPushforward_obj` — `Ru_{X/S, *}ℱ`
  and `Rf_{Zar, *}Ru_{X'/S, *}ℱ'` are concentrated in degrees `≥ 0`.
* `pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_07QA` — **the kernel half of
  [Stacks, Tag 07QA] on hypercohomology groups**, from the annihilation of [Stacks, Tag 07Q9]
  alone.
* `exists_hypercohomologyMap_eq_pow_smul_07QA` — **the cokernel half**, from the annihilation
  and `hmono`.
* `derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence` — **the identification
  of the comparison map with `f^*` is unconditional**:
  `...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison` with its hypothesis
  discharged by `...SmallSite.crisZariskiLerayCoherence`.  This is what makes the two bounds
  statements about `f^*` and not about an unrelated map.

## No tag is placed

No tag attribute is placed here.  Both theorems below take `...SmallSite.Annihilation07Q9` as
an input, so that they apply to any annihilator.  [Stacks, Tag 07Q9] is
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of `SmallSite/AlphaPCover07Q9Main.lean`,
and [Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, which supplies that annihilation and the one
monomorphism; the coherence square and the corepresentation used here take no hypothesis.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Both terms of the triangle are concentrated in degrees `≥ 0` -/

section IsGE

variable (T : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]

/-- **`Ru_{X/S, *}ℱ` is concentrated in degrees `≥ 0`.**  A right derived functor on `D⁺` moves
cohomology to the right, and `ℱ[0]` is concentrated in degrees `≥ 0`.

This is the first term of the triangle of [Stacks, Tag 07Q9], and the hypothesis the kernel bound
of [Stacks, Tag 07QA] has for free. -/
theorem isGE_derivedZariskiDirectImage_obj
    (F : Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) :
    ((derivedZariskiDirectImage T).obj F).IsGE 0 :=
  Functor.isGE_rightDerivedFunctorPlus_obj (zariskiDirectImage T) _ 0

end IsGE

section Bound

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory (Sheaf S'.smallTopology AddCommGrpCat)] in
/-- **`Rf_{Zar, *}Ru_{X'/S, *}ℱ'` is concentrated in degrees `≥ 0`**, the second term of the
triangle of [Stacks, Tag 07Q9]: two right derived functors on `D⁺` applied to a sheaf placed in
degree zero. -/
theorem isGE_derivedZariskiPushforward_obj
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj G)).IsGE 0 :=
  have := isGE_derivedZariskiDirectImage_obj S G
  Functor.isGE_rightDerivedFunctorPlus_obj (zariskiPushforward S S' fX) _ 0

/-- A distinguished triangle on the image of the comparison map in `D(Ab(X_Zar))`, with both
first terms concentrated in degrees `≥ 0` and third term annihilated by `q` in every degree. -/
private theorem exists_triangle_comparison_07QA (q : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F)) :
    ∃ (E : DerivedCategory (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
      (v : _ ⟶ E) (w : E ⟶ _⟦(1 : ℤ)⟧),
      Triangle.mk (DerivedCategory.Plus.ι.map
        (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F)) v w ∈
          distTriang (DerivedCategory (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})) ∧
      (DerivedCategory.Plus.ι.obj ((derivedZariskiDirectImage S').obj F)).IsGE 0 ∧
      (DerivedCategory.Plus.ι.obj ((derivedZariskiPushforwardFunctor S S' fX).obj
        ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))).IsGE 0 ∧
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj E) = 0 := by
  obtain ⟨E, v, wE, hT⟩ := distinguished_cocone_triangle
    (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F)
  have := isGE_derivedZariskiDirectImage_obj S' F
  have := isGE_derivedZariskiPushforward_obj S S' fX (crisPullback S S' fS fX hf F)
  exact ⟨_, _, _, DerivedCategory.Plus.ι.map_distinguished _ hT,
    inferInstance, inferInstance, smul_id_homologyFunctor_ι_obj₃_eq_zero S' q hann v wE hT⟩

variable [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- **The map `H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`** induced by the
comparison map of [Stacks, Tag 07Q9].  This is the map whose kernel and cokernel the two theorems
below bound; it is unconditional, the commutation of the square of topoi being
`...SmallSite.crisZariskiSquare`. -/
def zariskiHypercohomologyComparisonMap
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor S').obj
          ((derivedZariskiDirectImage S').obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor S').obj
          ((derivedZariskiPushforwardFunctor S S' fX).obj
            ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
    ((derivedZariskiGlobalSectionsFunctor S').map
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))

/-- **The kernel half of [Stacks, Tag 07QA] on Zariski hypercohomology groups.**  Given the
conclusion of [Stacks, Tag 07Q9] — that the third term of a distinguished triangle on the
comparison map has cohomology sheaves annihilated by `q` — the kernel of

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`

is annihilated by `q^{i + 1}`.

`hann` is the conclusion of [Stacks, Tag 07Q9] for the abelian comparison map, taken as an input
so that the bound applies to any annihilator; no tag attribute is placed on this lemma.
Everything else the bound needs is discharged: the concentration of both terms in degrees `≥ 0`
(`isGE_derivedZariskiDirectImage_obj`, `isGE_derivedZariskiPushforward_obj`), the comparison map
itself, and the identification of cohomology classes with morphisms out of `ℤ_X[0]⟦-i⟧`
(`...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` and its naturality). -/
theorem pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_07QA (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj ((derivedZariskiDirectImage S').obj F)))
    (hx : zariskiHypercohomologyComparisonMap S S' fS fX hf F i x = 0) :
    ((q : ℤ) ^ (i + 1)) • x = 0 := by
  set α := derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F
  obtain ⟨E, v, w, hT, h₁, h₂, hE⟩ := exists_triangle_comparison_07QA S S' fS fX hf q F hann
  set T := Triangle.mk (DerivedCategory.Plus.ι.map α) v w
  have : T.obj₁.IsGE 0 := h₁
  have : T.obj₂.IsGE 0 := h₂
  have hge : T.obj₃.IsGE (-1) := by
    have h := Stacks.Triangulated.isGE_obj₃_sub_one T hT 0
    rwa [zero_sub] at h
  have : (T.invRotate).obj₁.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_shift T.obj₃ (-1) (-1) 0 (by omega)
  have hW : ∀ j : ℤ, j ≤ (i : ℤ) →
      ((q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj (T.invRotate).obj₁) = 0) :=
    fun j _ => Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
      (((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).shiftIso (-1) j (j - 1)
          (by omega)).app T.obj₃) (hE (j - 1))
  have hkey : (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
        ((derivedZariskiDirectImage S').obj F) (i : ℤ)) x ≫
      DerivedCategory.Plus.ι.map α = 0 := by
    rw [← derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality S' α (i : ℤ) x,
      show (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
          ((derivedZariskiGlobalSectionsFunctor S').map α) x = 0 from hx]
    exact map_zero _
  have hg := pow_smul_eq_zero_of_kernel_07QA q i (T.invRotate)
    (inv_rot_of_distTriang T hT) hW (zariskiUnitShift S' (i : ℤ))
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
      ((derivedZariskiDirectImage S').obj F) (i : ℤ)) x) hkey
  apply (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
    ((derivedZariskiDirectImage S').obj F) (i : ℤ)).injective
  rwa [map_zsmul, map_zero]

/-- **The cokernel half of [Stacks, Tag 07QA] on Zariski hypercohomology groups.**  Given the
conclusion of [Stacks, Tag 07Q9] and that `ℋ^0` of the comparison map is a monomorphism,
`q^{i + 1}` times any class in `H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')` is in the image of

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`.

Two inputs are taken.  `hann` is the conclusion of [Stacks, Tag 07Q9], as in
`pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_07QA`.  `hmono` is the source's own observation
in the form the bound consumes it: the vanishing of `ℋ^{-1}` of the third term, equivalently the
injectivity of `ℋ^0` of the comparison, is what makes the exponent `q^{i + 1}` rather than
`q^{i + 2}`, and the module documentation of `SmallSite/AlphaPCoverTriangle.lean` records why
it holds for an iterated `α_p`-cover; for a crystal in quasi-coherent modules it is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.  No tag
attribute is placed on this lemma. -/
theorem exists_hypercohomologyMap_eq_pow_smul_07QA (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (hmono : Mono ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
        (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))))
    (y : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj
        ((derivedZariskiPushforwardFunctor S S' fX).obj
          ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))))) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y =
      zariskiHypercohomologyComparisonMap S S' fS fX hf F i x := by
  set α := derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F
  obtain ⟨E, v, w, hT, h₁, h₂, hE⟩ := exists_triangle_comparison_07QA S S' fS fX hf q F hann
  set T := Triangle.mk (DerivedCategory.Plus.ι.map α) v w
  have : T.obj₁.IsGE 0 := h₁
  have : T.obj₂.IsGE 0 := h₂
  obtain ⟨h, hh⟩ := exists_comp_mor₁_eq_pow_smul_07QA_of_mono q i T hT hmono (fun j _ => hE j)
    (zariskiUnitShift S' (i : ℤ))
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
      ((derivedZariskiPushforwardFunctor S S' fX).obj
        ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))) (i : ℤ)) y)
  refine ⟨(derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
    ((derivedZariskiDirectImage S').obj F) (i : ℤ)).symm h, ?_⟩
  apply (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
    ((derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))) (i : ℤ)).injective
  have e2 := derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality S' α (i : ℤ)
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
      ((derivedZariskiDirectImage S').obj F) (i : ℤ)).symm h)
  refine (map_zsmul _ _ _).trans (hh.trans (Eq.trans ?_ e2.symm))
  exact congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map α)
    (AddEquiv.apply_symm_apply _ h).symm

/-! ### The identification of the comparison map with `f^*` is unconditional -/

/-- **`RΓ(X_Zar, -)` of the comparison map of [Stacks, Tag 07Q9] *is* `f^*`, with nothing
carried.**  This is
`...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison` of
`SmallSite/LerayCoherence.lean` with its one hypothesis discharged by
`...SmallSite.crisZariskiLerayCoherence` of `SmallSite/UnderivedLerayCoherence.lean`.

The square says that `RΓ(X_Zar, -)` applied to `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` is
`...SmallSite.derivedCrisPullbackMap`, read through the Leray factorization of
`RΓ(Cris(X/S), -)` along `u_{X/S}` on the source and through the factorizations along `u_{X'/S}`
and `f_{Zar}` on the target.  It is the third of the three inputs the docstring of
`...SmallSite.crisCohomologyMap` names, and the one that is *not* a consequence of the square of
topoi together with [Stacks, Proposition 07LG]; recording it here with no hypothesis is what
makes the two bounds above statements about `f^*` rather than about an unrelated map.

So the remaining inputs of 07QA are the annihilation of [Stacks, Tag 07Q9], resting on
[Stacks, Proposition 07LG], and the monomorphism of the cokernel half, both supplied in
`SmallSite/CrisCohomologyBound07QAMain.lean`. -/
theorem derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (derivedGlobalSectionsIsoDerivedZariskiDirectImage S').hom.app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (derivedZariskiGlobalSectionsFunctor S').map
          (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F) =
      derivedCrisPullbackMap S S' fS fX hf F ≫
        (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
              (crisPullback S S' fS fX hf F)) ≫
        (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom.app
          ((derivedZariskiDirectImageFunctor S).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
                (crisPullback S S' fS fX hf F))) :=
  derivedZariskiGlobalSections_map_derivedZariskiComparison S S' fS fX hf
    (crisZariskiLerayCoherence S S' fS fX hf) F

end Bound

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
