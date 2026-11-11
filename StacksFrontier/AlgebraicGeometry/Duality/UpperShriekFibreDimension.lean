module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound

/-!
# The relative dualizing complex vanishes below minus the fibre dimension

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`,
the category of schemes separated and of finite type over `S` of [Stacks, Tag 0F42]. Let `x ∈ X`
with image `y ∈ Y`. This file reduces [Stacks, Tag 0BV5] (Lemma 48.21.3),

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i`,

to an affine chart through `x`, where `f^!` is `Stacks.Duality.upperShriek`, `𝒪_Y` is
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf` and `dim_x(X_y)` is the local
dimension of the scheme-theoretic fibre of `f` through `x`, at `x`. The lemma itself, with the
chart description supplied, is
`Stacks.Duality.exists_fibreDim_eq_and_neg_le_of_nontrivial_stalk_homology_upperShriek` in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekFibreDimensionCharts.lean`.

## Main results

* `Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek` — the bound, given
  the chart description of `f^!𝒪_Y` at a chart through `x`.
* `Stacks.Duality.nontrivial_stalk_homology_iff_nontrivial_localizedHomology` — the stalk
  dictionary of a tilde model: the stalk of `H^i(K)` at a point of an affine open `U` is
  nontrivial exactly when the localization of `H^i(ω)` at the corresponding prime of `Γ(X, U)`
  is, for `ω` a complex whose associated sheaf is `K|_U`.
* `Stacks.Duality.nontrivial_tilde_stalk_iff` — the stalk of `M^~` at a prime is the
  localization of `M` there.

## Implementation notes

*The source's proof.* It reads: the statement is local on `X`, so one may assume `X = Spec(A)`
and `Y = Spec(R)` affine; then `f^!𝒪_Y` is the relative dualizing complex `ω^•_{A/R}` of
[Stacks, Tag 0E9M] by Remark [Stacks, Tag 0BV2]; and the lemma is [Stacks, Tag 0E9P]. So the
cited inputs are exactly 0E9M, 0BV2 and 0E9P.

*The chart input.* The theorem here takes `h0BV2`, in the same shape as
`Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf`
([Stacks, Tag 0B6U] (a)): on an affine open `U ∋ x` of `X` inside the preimage of an affine open
`V` of `Y`, the restriction of `f^!𝒪_Y` to `U` is the associated sheaf of the *algebraic* upper
shriek, along a polynomial presentation of the chart ring map `f.appLE V U`, of `Γ(Y, V)` placed
in degree zero. That is the affine identification of the source's Remark [Stacks, Tag 0BV2],
proved for every chart as `Stacks.Duality.upperShriekStructureSheafCharts`; the file
`UpperShriekFibreDimensionCharts.lean` discharges `h0BV2` with it.

Everything the conclusion asserts is proved here, from

* [Stacks, Tag 0E9P],
  `Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology`,
  which is the bound `-d ≤ i` for the algebraic upper shriek of an arbitrary polynomial
  presentation, with `d` the relative dimension of the chart algebra at the prime; and
* the two dictionaries the reduction to the chart needs: the stalk of `H^i(f^!𝒪_Y)` at `x` is
  the localization at that prime of `H^i` of the algebraic complex
  (`Stacks.Duality.nontrivial_stalk_homology_iff_nontrivial_localizedHomology` below), and the
  local dimension of the scheme-theoretic fibre at `x` is the relative dimension of the chart
  algebra at that prime (
  `Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt`).

*[Stacks, Tag 0E9Q] is not used here.* It is not needed for Tag 0BV5 — the source's proof of
0BV5 cites only 0E9M, 0BV2 and 0E9P, as quoted above. Tag 0E9Q is the input to the *flat*
refinement [Stacks, Tag 0BV6], which adds the upper bound `i ≤ 0` and the tor-amplitude
statement, and is not claimed here.

The library does state Tag 0E9Q at the ring level: the local bounds are
`Dualizing.upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology` and the
concentration under a uniform fibre-dimension bound is
`Dualizing.isZero_homology_upperShriekFunctor_unit_of_notMem_Icc`, both of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper`, and the Tor-amplitude
clause is `Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitude`. Those are consumed
by the flat refinement in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekFibreDimensionFlat.lean`, not here.

*Why the statement is global even though the source's argument is affine.* The locality of the
statement is carried by `h0BV2` itself: it provides the affine chart at `x` together with the
identification on it, and the two dictionaries above transport the hypothesis and the conclusion
between `x` and the corresponding prime of `Γ(X, U)`. No affineness is assumed of `X` or `Y`.

*The two derived categories.* `Stacks.Duality.upperShriek` lives on
`Stacks.Duality.quasiCoherentDerivedCategory`, read at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, while the derived category of a chart ring
is read at `CategoryTheory.HasDerivedCategory.standard`. As in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekBounded.lean`, the two are never compared: the
derived universes keep them apart and the only traffic between them is through `h0BV2` and the
sheafification functor `AlgebraicGeometry.tilde.functor`.

## References

* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0E9P](https://stacks.math.columbia.edu/tag/0E9P)
* [Stacks Project, Tag 0E9M](https://stacks.math.columbia.edu/tag/0E9M)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

/-! ### Nontriviality transports along isomorphisms of abelian groups -/

/-- Nontriviality of the underlying type of an object of `Ab` only depends on its isomorphism
class. -/
theorem nontrivial_iff_of_abIso {A B : Ab.{u}} (e : A ≅ B) : Nontrivial A ↔ Nontrivial B :=
  ((forget Ab.{u}).mapIso e).toEquiv.nontrivial_congr

/-! ### The stalk of an associated sheaf is a localization -/

section TildeStalk

variable {R : CommRingCat.{u}}

/-- **The stalk of `M^~` at a prime `𝔮` is the localization `M_𝔮`.** Both are localizations of
`M` at the prime complement of `𝔮`: the stalk because `AlgebraicGeometry.tilde.toStalk` is a
localization map, and `LocalizedModule` by construction. -/
theorem nontrivial_tilde_stalk_iff (M : ModuleCat.{u} R) (q : PrimeSpectrum R) :
    Nontrivial ((tilde M).presheaf.stalk q) ↔
      Nontrivial (LocalizedModule q.asIdeal.primeCompl (M : Type u)) := by
  have : q.asIdeal.IsPrime := q.isPrime
  exact (IsLocalizedModule.iso q.asIdeal.primeCompl
    (AlgebraicGeometry.tilde.toStalk M q).hom).toEquiv.nontrivial_congr.symm

end TildeStalk

/-! ### The stalk of the cohomology of a tilde model -/

section StalkModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- **The stalk dictionary of a tilde model.** If `K|_U` is the associated sheaf of the complex
`ω` over `Γ(X, U)` on an affine open `U ∋ x`, then the stalk of `H^i(K)` at `x` is nontrivial
exactly when the localization of `H^i(ω)` at the prime of `Γ(X, U)` corresponding to `x` is.

The chain is: the stalk of `H^i(K)` at `x` is the stalk at `x` read in `U` of `H^i(K)|_U`
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), which by the tilde model is the stalk
of the pullback along `U ≅ Spec Γ(X, U)` of `H^i(ω)^~`
(`Stacks.Duality.homologyRestrictIsoTilde`), which is the stalk of `H^i(ω)^~` at the
corresponding prime (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`restrictStalkNatIso` again), which is the localization of `H^i(ω)`
(`Stacks.Duality.nontrivial_tilde_stalk_iff`). -/
theorem nontrivial_stalk_homology_iff_nontrivial_localizedHomology
    {K : DerivedCategory X.Modules} {U : X.Opens} (hU : IsAffineOpen U)
    {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))}
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)
    (x : U.toScheme) (q : PrimeSpectrum Γ(X, U)) (hq : hU.isoSpec.hom x = q) (i : ℤ) :
    Nontrivial
        (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk (U.ι x)) ↔
      Nontrivial (LocalizedModule q.asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω : Type u)) := by
  subst hq
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω
  let F := (DerivedCategory.homologyFunctor X.Modules i).obj K
  have e₁ : ((Scheme.Modules.restrictFunctor U.ι).obj F).presheaf.stalk x ≅
      F.presheaf.stalk (U.ι x) :=
    (Scheme.Modules.restrictStalkNatIso U.ι x).app F
  have e₂ : ((Scheme.Modules.restrictFunctor U.ι).obj F).presheaf.stalk x ≅
      ((Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde N)).presheaf.stalk x :=
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      ((Scheme.Modules.toPresheaf U.toScheme).mapIso (homologyRestrictIsoTilde hU e i))
  have e₃ : ((Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj (tilde N)).presheaf.stalk x ≅
      ((Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde N)).presheaf.stalk x :=
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      ((Scheme.Modules.toPresheaf U.toScheme).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app (tilde N)))
  have e₄ : ((Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj (tilde N)).presheaf.stalk x ≅
      (tilde N).presheaf.stalk (hU.isoSpec.hom x) :=
    (Scheme.Modules.restrictStalkNatIso hU.isoSpec.hom x).app (tilde N)
  exact (nontrivial_iff_of_abIso e₁).symm.trans ((nontrivial_iff_of_abIso e₂).trans
    ((nontrivial_iff_of_abIso e₃).symm.trans ((nontrivial_iff_of_abIso e₄).trans
      (nontrivial_tilde_stalk_iff N (hU.isoSpec.hom x)))))

end StalkModel

/-! ### Tag 0BV5 -/

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The bound of Tag 0BV5 from a chart description.** Let `f : X ⟶ Y` be a morphism of
`FTS S` and `x ∈ X`. Given an affine chart `U ∋ x` inside the preimage of an affine open `V` of
`Y` on which `f^!𝒪_Y` is the associated sheaf of the algebraic upper shriek of `Γ(Y, V)` along a
polynomial presentation of `f.appLE V U` (`h0BV2`), and a natural number `d` equal to the local
dimension `dim_x(X_y)` of the scheme-theoretic fibre, `H^i(f^!𝒪_Y)_x ≠ 0 ⟹ -d ≤ i`.

The chart description holds at every chart: it is `Stacks.Duality.upperShriekStructureSheafCharts`
([Stacks, Tag 0BV2] for `𝒪_Y`), and [Stacks, Tag 0BV5] without these inputs is
`Stacks.Duality.exists_fibreDim_eq_and_neg_le_of_nontrivial_stalk_homology_upperShriek`. The
bound itself is [Stacks, Tag 0E9P] for the algebraic upper shriek, moved to the chart by the stalk
dictionary `Stacks.Duality.nontrivial_stalk_homology_iff_nontrivial_localizedHomology` and the
fibre-dimension dictionary `Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt`.
-/
theorem neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek (x : X.left)
    (h0BV2 : ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i := by
  obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := h0BV2
  have hN (Z : AlgebraicGeometry.FTS S) : IsLocallyNoetherian Z.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hVn : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  -- The prime of the chart ring corresponding to `x`.
  let q : PrimeSpectrum Γ(X.left, U) := hU.primeIdealOf ⟨x, hxU⟩
  -- The fibre-dimension dictionary.
  have hdq : Algebra.relativeDimensionAt Γ(Y.left, V) q.asIdeal = (d : WithBot ℕ∞) := by
    rw [← hd]
    exact (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV x hxU).symm
  -- The stalk dictionary.
  have hloc := (nontrivial_stalk_homology_iff_nontrivial_localizedHomology hU he.some
    (⟨x, hxU⟩ : U.toScheme) q rfl i).mp hi
  -- Tag 0E9P on the chart.
  exact Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
    p q d hdq i hloc

end Shriek

end Stacks.Duality

end
