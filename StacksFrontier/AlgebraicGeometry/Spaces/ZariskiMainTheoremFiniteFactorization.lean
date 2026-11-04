module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralMorphismDirectedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral

/-!
# Zariski's main theorem for algebraic spaces: the finite factorization

Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces over a scheme `S`,
with `Y` quasi-compact and quasi-separated. Zariski's main theorem in the form of Stacks 082K
says that `f` factors as `X --j--> T --π--> Y` with `j` a quasi-compact open immersion and `π`
finite.

The proof is the source's. By Stacks 082J the normalization `X --f'--> Y' --ν--> Y` of `Y` in
`X` has `f'` a quasi-compact open immersion and `ν` integral. As `Y` is quasi-compact and
quasi-separated, `Y'` is a directed limit `Y' = lim T_i` of algebraic spaces finite and of
finite presentation over `Y` (Stacks 09YA); the transition morphisms are affine, because a
morphism between spaces finite over `Y` is finite, and the stages are quasi-separated. So `X`
maps by an immersion to some `T_i`, quasi-compactly; Stacks 081U factors that immersion as an
open immersion `X ⟶ T` followed by a closed immersion `T ⟶ T_i`, and `T ⟶ T_i ⟶ Y` is finite.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite`:
  **Stacks 082K**, the factorization.

## Implementation notes

The source writes `ν_* 𝒪_{Y'}` as the directed colimit of its finite quasi-coherent
`𝒪_Y`-subalgebras `𝒜_i` (Stacks 082C) and takes `T_i = \underline{Spec}_Y(𝒜_i)`, so that
`Y' = lim T_i` with affine transition morphisms. That inverse system is what Stacks 09YA, which
the source also cites, provides for the integral morphism `ν`; its stages are moreover of finite
presentation over `Y`, which is not needed. The system is the one of Stacks 09YA,
`AlgebraicGeometry.Space.integralFiniteSystemOfIsIntegralHom`.

The source finds the immersion into a stage in three moves: it descends the quasi-compact open
`f'(X) ⊆ Y'` to a quasi-compact open `U_i ⊆ T_i` (Stacks 0827), identifies `X` with the limit of
the inverse images `U_{i'}` (Stacks 07SF), and makes `X ⟶ U_{i'}` a closed immersion for large
`i'` (Stacks 0828, part (1)). Those three moves are exactly the proof of Stacks 0828, part (2),
for the immersion `f' : X ⟶ Y' = lim T_i`, whose source `X` is quasi-compact and locally of
finite type over `Y` and whose stages are quasi-separated; so part (2) is applied directly. It
has no bound on the size of the index set, which matters here because the index set of Stacks
09YA carries none.

## References

* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 082J](https://stacks.math.columbia.edu/tag/082J)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 082K, Zariski's main theorem, the finite factorization.** Let
`f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated. Then `f = π ∘ j` with `j : X ⟶ T` a quasi-compact open
immersion into an algebraic space `T` and `π : T ⟶ Y` finite. -/
@[stacks 082K]
theorem exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : X ⟶ T) (π : T ⟶ Y),
      IsAlgebraicSpace B S hS T ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
        IsFinite B S hS π ∧ j ≫ π = f := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  -- Stacks 082J: the normalization `X ⟶ Y' ⟶ Y`.
  obtain ⟨-, N, hfac, hopen, -, hint⟩ := zariskiMainTheorem B S hS f hX hY hqf hsep
  -- Stacks 09YA: `Y' = lim T_i` with `T_i` finite and of finite presentation over `Y`.
  let P := integralFiniteSystemOfIsIntegralHom B S hS N.fromNorm N.isAlgebraicSpace hY
    hint hYqc hYqs
  let : Preorder P.indexType := P.indexPreorder
  let : Nonempty P.indexType := P.indexNonempty
  let : IsDirected P.indexType (· ≤ ·) := P.indexDirected
  have htransition : ∀ ⦃i j : P.indexType⦄ (h : i ≤ j),
      IsAffineHom B S hS (P.diagram.map (homOfLE h).op) := by
    intro i j h
    have hfin : IsFinite B S hS (P.diagram.map (homOfLE h).op ≫ P.structureMap.app (op i)) := by
      rw [P.structureMap.naturality (homOfLE h).op]
      simpa using P.stageFinite (op j)
    exact IsFinite.isAffineHom (isFinite_of_comp_of_isSeparated B S hS _ _ hfin
      (isSeparated_of_isFinite B S hS _ (P.stageAlgebraicSpace (op i)) hY (P.stageFinite (op i))))
  have hstageQS : ∀ i, IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
      (P.diagram.obj (op i)) := fun i =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (P.stageAlgebraicSpace (op i)) hYqs
      (P.stageFinitePresentation (op i)).2.2
  have hcommutes : (Cone.mk N.space P.limitCone).π ≫ P.structureMap =
      (Functor.const P.indexTypeᵒᵖ).map N.fromNorm :=
    NatTrans.ext (funext fun i => (P.compatible i).symm)
  -- `X` is quasi-compact and locally of finite type over `Y`.
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hqf.2
  have hft : IsLocallyOfFiniteType B S hS (N.toNorm ≫ N.fromNorm) := by
    rw [hfac]
    exact fun U V a b h ha hb hcomm => (hqf.1 U V a b h ha hb hcomm).1
  -- Stacks 0828, part (2): `X ⟶ T_i` is an immersion for some `i`.
  obtain ⟨i, hi⟩ := (eventually_isImmersion_comp_limitπ B S hS Y hY P.diagram
    (fun i => P.stageAlgebraicSpace (op i)) P.structureMap (Cone.mk N.space P.limitCone)
    P.isLimit N.fromNorm hcommutes X hX hXqc N.toNorm htransition hstageQS hft
    (isImmersion_of_isOpenImmersion B S hS hopen)).exists
  let q : X ⟶ P.diagram.obj (op i) := N.toNorm ≫ P.limitCone.app (op i)
  -- Stacks 081U: `X ⟶ T ⟶ T_i`, an open immersion followed by a closed immersion.
  obtain ⟨T, j, ι, hT, hj, hι, hjι⟩ :=
    exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact B S hS
      (P.stageAlgebraicSpace (op i)) q hi
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (P.stageAlgebraicSpace (op i))
        (hstageQS i) hXqc q)
  have hπ : IsFinite B S hS (ι ≫ P.structureMap.app (op i)) :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS ι hι) (P.stageFinite (op i))
  refine ⟨T, j, ι ≫ P.structureMap.app (op i), hT, hj,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hT
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hT hYqs
        (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isFinite B S hS _ hT hY hπ)))
      hXqc j, hπ, ?_⟩
  rw [← Category.assoc, hjι, Category.assoc, ← P.compatible, hfac]

end AlgebraicGeometry.Space

end
