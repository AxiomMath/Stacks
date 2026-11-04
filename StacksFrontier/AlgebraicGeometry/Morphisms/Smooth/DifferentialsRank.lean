module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth
public import StacksFrontier.RingTheory.Kaehler.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of the differentials of a smooth morphism

For a smooth morphism of schemes, the rank at a point of the sheaf of relative differentials
equals the local dimension at that point of the scheme-theoretic fibre through it.

## Main results

* `AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt` identifies the rank
  at a point of the stalk of the sheaf of relative differentials with the local fibre dimension.

## Implementation notes

The rank at a point is the `Module.finrank` of the stalk of the sheaf of relative differentials
over the stalk of the structure sheaf of the source; it is coerced into `WithBot ℕ∞`, the
codomain of the local topological Krull dimension. The point of the fibre over the image
determined by the point itself is `AlgebraicGeometry.Scheme.Hom.asFiber`.

Smoothness produces affine charts on which the map of coordinate rings is standard smooth, hence
carries a submersive presentation. Both sides are computed from that presentation: the stalk of
the differentials is the module of Kähler differentials of the stalk map, which is a localization
of the Kähler differentials of the chart and therefore free on the complement of the image of the
presentation's index map; and the local fibre dimension is the same cardinality.

## References

* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 00RT](https://stacks.math.columbia.edu/tag/00RT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry

/-- For a submersive presentation of `B` over `A`, the Kähler differentials of a localization
`B'` of `B` at a prime, taken relative to a localization `A₀` of `A`, are free of rank the
dimension of the presentation. -/
private lemma finrank_kaehlerDifferential_localization
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra B B']
    [Algebra A B'] [IsScalarTower A B B'] (T : Submonoid A) (A₀ : Type u) [CommRing A₀]
    [Algebra A A₀] [IsLocalization T A₀] [Algebra A₀ B'] [IsScalarTower A A₀ B']
    {q : Ideal B} [q.IsPrime] [IsLocalization.AtPrime B' q]
    {ι σ : Type} [Finite ι] [Finite σ] (P : Algebra.SubmersivePresentation A B ι σ) :
    Module.finrank B' Ω[B'⁄A₀] = P.dimension := by
  classical
  have : IsLocalRing B' := IsLocalization.AtPrime.isLocalRing (R := B) (S := B') q
  have : IsLocalizedModule q.primeCompl (KaehlerDifferential.map A A B B') :=
    omega_localization_total A B q.primeCompl B'
  let b : Module.Basis ((Set.range P.map)ᶜ : Set ι) B' Ω[B'⁄A] :=
    P.basisKaehler.ofIsLocalizedModule B' q.primeCompl (KaehlerDifferential.map A A B B')
  let e : Ω[B'⁄A] ≃ₗ[B'] Ω[B'⁄A₀] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map A A₀ B' B')
      (omega_localization_base A B' T A₀)
  exact (Module.finrank_eq_nat_card_basis (b.map e)).trans (natCard_compl_range_map P)

/-- **Stacks Project, Tag 02G1.** For a smooth morphism of schemes, the rank at a point of the
sheaf of relative differentials is the local dimension of the fibre at that point. -/
@[stacks 02G1 "differentials_rank_eq_fibre_dimension",
  ega "IV 17.10.2" "rank_x = dim_x f",
  sga "3 XI 1.9" "rank = fiber dimension",
  sga "1 II 4.3" "(ii) rank formula",
  ega "IV 17.15.5" "a) => c) rank",
  ega "IV 17.15.15" "smooth ⇒ rank=dim_x f"]
theorem finrank_stalk_relativeDifferentials_eq_fiberDimensionAt {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] (x : X) :
    (Module.finrank (ToType (X.sheaf.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf x)) : WithBot ℕ∞) =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hxU : f x ∈ U := hVU hxV
  let A := ToType Γ(S, U)
  let B := ToType Γ(X, V)
  let A₀ := ToType (S.presheaf.stalk (f x))
  let B₀ := ToType (X.sheaf.presheaf.stalk x)
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxV⟩
  let algAB : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let algAA₀ : Algebra A A₀ := (S.presheaf.germ U (f x) hxU).hom.toAlgebra
  let algBB₀ : Algebra B B₀ := (X.presheaf.germ V x hxV).hom.toAlgebra
  let algA₀B₀ : Algebra A₀ B₀ := algebraStalkMap f x
  let algAB₀ : Algebra A B₀ := ((algebraMap A₀ B₀).comp (algebraMap A A₀)).toAlgebra
  have : IsScalarTower A A₀ B₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcompat : f.appLE U V hVU ≫ X.presheaf.germ V x hxV =
      S.presheaf.germ U (f x) hxU ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVU) x hxV]
    exact (Scheme.Hom.germ_stalkMap f U x hxU).symm
  have : IsScalarTower A B B₀ := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    show (f.stalkMap x).hom ((S.presheaf.germ U (f x) hxU).hom a) = _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat.symm) a
  have : IsLocalization.AtPrime A₀ p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization.AtPrime B₀ q.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hsm : Algebra.IsStandardSmooth A B := hstd.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hsm.out
  have hdim := fiberDimensionAt_eq_of_submersivePresentation f x ⟨V, hV⟩ ⟨U, hU⟩ hxV hVU rfl P
  have hrank : Module.finrank B₀ Ω[B₀⁄A₀] = P.dimension :=
    finrank_kaehlerDifferential_localization (q := q.asIdeal) p.asIdeal.primeCompl A₀ P
  have hstalk : Module.finrank B₀
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x)) = Module.finrank B₀ Ω[B₀⁄A₀] :=
    (relativeDifferentialsStalkKaehlerEquiv f x).finrank_eq
  rw [hdim, hstalk, hrank]
  rfl

end AlgebraicGeometry
