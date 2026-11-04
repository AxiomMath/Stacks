module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinIdentification
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.CompletedStalkRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ClassifyingIsIso
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ExceptionalFibre

/-!
# Contracting an exceptional curve of the first kind

**[Stacks, Tag 0C2L].** Let `X` be a Noetherian scheme and let `E ⊂ X` be an exceptional curve
of the first kind. If there is a morphism `f : X ⟶ Y` such that `Y` is Noetherian, `f` is proper,
`f` maps `E` to a point `y` of `Y`, and `f` is quasi-finite at every point not in `E`, then there
exists a contraction of `E`, and it is the Stein factorization of `f`.

The proof is the source's. After replacing `f` by the first factor `f' : X ⟶ Y'` of its Stein
factorization (`AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup`),
`f'_* 𝒪_X = 𝒪_{Y'}` and the fibres of `f'` are geometrically connected, so

* the set-theoretic fibre over `y` is `E`;
* the completion of `𝒪_{Y', y}` is the ring `lim H⁰(Eₙ, 𝒪)` of [Stacks, Tag 0C2K], so `𝒪_{Y', y}`
  is regular of dimension two;
* the scheme-theoretic fibre over `y` is `E`, so `f'` factors through the blowup of `Y'` at `y`;
* the factoring morphism is an isomorphism.

## Main results

* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_isSteinFactorization` —
  **[Stacks, Tag 0C2L]**: a contraction of `E` exists and it is the Stein factorization of `f`,
  the latter given by its characterisation in [Stacks, Tag 03H0].
* `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization` — the same with the Stein
  factorization named: the first factor `f.toNormalization` is a contraction of `E`.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry


/-- **The first factor of the Stein factorization contracts an exceptional curve of the first
kind** ([Stacks, Tag 0C2L], with the Stein factorization `f = f.toNormalization ≫
f.fromNormalization` of [Stacks, Tag 03H0] named). Let `X` be Noetherian, `E ⊆ X` an exceptional
curve of the first kind cut out by `D` and presented as `𝐏¹_k` by `e`, and `f : X ⟶ Y` a proper
morphism to a Noetherian scheme carrying `E` to a point `y` and quasi-finite at every point off
`E`. Then `f.toNormalization` is a contraction of `E`. -/
public theorem isContractionOfExceptionalCurve_toNormalization
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u}
    [Field k] {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x) :
    IsContractionOfExceptionalCurve D f.toNormalization := by
  have := isReduced_subscheme_of_projectiveLineProj_iso k e
  have hA :=
    Scheme.IdealSheafData.isRegularLocalRing_formalNeighborhoodRing_of_isExceptionalCurveOfFirstKind
      hE
  open Scheme.IdealSheafData in
  have h₂ := ringKrullDim_formalNeighborhoodRing_eq_two_of_isExceptionalCurveOfFirstKind hE
  refine isContractionOfExceptionalCurve_toNormalization_of_steinSetup hE f y hmaps hqf
    (fun Y' f' y' hs ↦ ?_) (fun Y' f' y' hs ↦ ?_) (fun Y' f' y' hs hy' ↦ ?_)
    (fun Y' f' y' hs hy' g hg ↦
      isIso_blowUpClassifying_of_steinSetup_of_isNoetherian hE f' y' hs hy' ?_ ?_ ?_ g hg)
  all_goals
    have hmaps' : ∀ x ∈ (D.support : Set X), f'.base x = y' :=
      (D.forall_subschemeι_base_eq_iff_forall_mem_support f' y').1 hs.base_eq
    have hfib' := preimage_singleton_subset_support_of_steinSetup e f' y' hs
    first
    | exact Scheme.IdealSheafData.isRegularLocalRing_stalk_of_steinSetup e f' y' hs hmaps' hfib' hA
    | exact (Scheme.IdealSheafData.ringKrullDim_stalk_eq_of_steinSetup e f' y' hs hmaps'
        hfib').trans h₂
    | exact eq_comap_vanishingIdeal_singleton_of_le_map_maximalIdeal hE f' y' hy' hmaps' hfib'
        (Scheme.IdealSheafData.formalNeighborhoodFiltration_one_eq_map_maximalIdeal_of_steinSetup
          hE f' y' hs hmaps' hfib').le

/-- **Stacks Project, Tag 0C2L.** Let `X` be a Noetherian scheme and `E ⊆ X` an exceptional curve
of the first kind, cut out by `D` and presented as `𝐏¹_k` by `e`. Let `f : X ⟶ Y` be a morphism
such that `Y` is Noetherian, `f` is proper, `f` maps `E` to a point `y` of `Y`, and `f` is
quasi-finite at every point not in `E`. Then there exists a contraction `b : X ⟶ Z` of `E`, and it
is the Stein factorization of `f`: `f = b ≫ π` with `𝒪_Z ⟶ b_* 𝒪_X` an isomorphism and `π`
integral, which characterises the Stein factorization ([Stacks, Tag 03H0]). -/
@[stacks 0C2L]
public theorem exists_isContractionOfExceptionalCurve_isSteinFactorization
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u}
    [Field k] {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z) (π : Z ⟶ Y), b ≫ π = f ∧ IsIso b.c ∧ IsIntegralHom π ∧
      IsContractionOfExceptionalCurve D b :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization,
    Stacks.SteinFactorization.toNormalization_fromNormalization f,
    Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f,
    Stacks.SteinFactorization.isIntegralHom_fromNormalization f,
    isContractionOfExceptionalCurve_toNormalization hE f y hmaps hqf⟩

end AlgebraicGeometry

end
