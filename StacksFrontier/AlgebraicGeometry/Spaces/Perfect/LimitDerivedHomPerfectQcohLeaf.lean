module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafUnitReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimQcohPull
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineSystemDerivedColimit

/-!
# Stacks 09RI

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  Stacks 09RI asserts that

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism if either (1) `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or (2) `E₀`
is pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension.

The source proves clause (1) by the induction principle of Stacks 08GP, which reduces it to the
case of an affine object `U` étale over `X₀`, and settles that case by the scheme-level
Stacks 09RE.  The induction is
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_qcohUnit`,
whose remaining input is the colimit statement on the base-changed system `U_i = X_i ×_{X₀} U`
for the pair `(𝒪_U, L)` at every shift of `𝒪_U`, `L` in `D_QCoh(𝒪_U)`.  This file proves that
input — for every affine algebraic space over `X₀`, étale or not — and with it the tag.

The input is reached by reading the base-changed system on its affine models through
`AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_representedAffine`
and computing there:
`AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj_derivedAssociated` is the
colimit statement at the structure sheaf and an arbitrary derived associated module along a
directed system of affine representables, which is the affine case of Stacks 09RE read over the
base ring.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite`:
  **the affine leaf of Stacks 09RI**: on the base-changed system of an affine algebraic space
  over `X₀`, the colimit statement for `(𝒪_U⟦n⟧, L)` for every `n` and every `L` in
  `D_QCoh(𝒪_U)`.
* `AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_mk_lt_cof_ord`:
  both clauses of Stacks 09RI, with the Tor condition of clause (2) read along any derived
  tensor product `T` on the site.

The statement with the Tor condition read along the derived tensor product `⊗^L_{𝒪_{X₀}}` of
Stacks 06YU is
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_smallEtale`
of `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomSmallEtaleTensor.lean`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The affine leaf of Stacks 09RI.**  In Situation 09RH with `#I` below the cofinality of the
cutoff, let `g : U ⟶ X₀` be a morphism from an affine algebraic space and let `L` lie in
`D_QCoh(𝒪_U)`.  Then on the base-changed system `U_i = X_i ×_{X₀} U`, for every `n`,

`colim_{i ≥ 0} Hom_{D(𝒪_{U_i})}(𝒪_{U_i}⟦n⟧, L_i) ⟶ Hom_{D(𝒪_{X ×_{X₀} U})}(𝒪⟦n⟧, L|)`

is bijective.  No étaleness of `g` is needed. -/
theorem shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite
    (hI : Cardinal.mk I < B.cutoff.ord.cof) {V : AlgebraicSpaces B S hS}
    (g : V ⟶ D.stage D.base) (hV : IsAffineSpace B S hS V.1) (L : derivedModules B S hS V)
    (hL : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS V.1 V.2) n).obj
      L).IsQuasicoherentOnSite) :
    PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem g)
      (smallEtaleDerivedPullbackData B S hS)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
        (SheafOfModules.unit _)) L :=
  shiftedIsColim_baseChangeSystem_unit_of_representedAffine (D := D) hI g hV L hL
    fun Sys hring hid p N => Sys.isColim_unitObj_derivedAssociated hid hring p N

/-- **Stacks 09RI along an arbitrary derived tensor product.**  In Situation 09RH, let `E₀` and
`K₀` be objects of `D(𝒪_{X₀})`, put `E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for `i ≥ 0` and
`E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  If either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or
`E₀` is pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension with
respect to the derived tensor product `T`, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism.

This is
`isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_qcohUnit`
with its hypothesis `hunit` discharged by
`shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite`,
so both clauses of the tag are proved at its own hypotheses.

The two restrictions beyond the tag are counterexample-forced for this formalization:
`I : Type u` is refuted beyond it by
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`, and
`#I < B.cutoff.ord.cof` by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`.  `T`
is the derived tensor product the Tor condition of clause (2) is predicated on, not an added
assumption. -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_mk_lt_cof_ord
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hcase :
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPerfect E₀ ∧
          ∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∨
        ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPseudoCoherent E₀ ∧
          (∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∧
          Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K₀)) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  D.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_qcohUnit E₀ K₀
    hI (fun u _ hV hqc => D.shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite hI u hV
      _ hqc) T hcase

end DescentSituation

end AlgebraicGeometry.Space

end
