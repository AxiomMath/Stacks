module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomNineRICarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback

/-!
# Clause (1) of Stacks 09RI with the quasi-coherence hypothesis of the tag

In Situation 09RH the hypothesis of
`AlgebraicGeometry.Space.DescentSituation.isColim_of_structureSheafAffineBaseChange` is the
colimit statement for the pair `(𝒪_U, Lu^*K₀)` over the objects `u : U ⟶ X₀` of the small étale
site with `U` affine, asked for an *arbitrary* `K₀`.  In that generality it is not available: the
route to it puts `Lu^*K₀` in the image of `𝒪_U ⊗_A -`, which needs `Lu^*K₀` to lie in
`D_QCoh(𝒪_U)`.  Clause (1) of Stacks 09RI does assume `K₀ ∈ D_QCoh(𝒪_{X₀})`, so the reachable
statement asks for the leaf only at the quasi-coherent objects — and then has to know that
`Lu^*K₀` is one of them.

That is Stacks 08F4, already available for every morphism of algebraic spaces as
`AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`; no étale
hypothesis is needed for it.  This file is the restatement it unlocks: the leaf hypothesis is
quantified over the objects of `D(𝒪_U)` whose cohomology sheaves are quasi-coherent, and the
quasi-coherence of `Lu^*K₀` that feeds it is supplied by 08F4 from the quasi-coherence of `K₀`.

As in the file it restates, the colimit statement at the structure sheaf is **not** proved here
but carried as a hypothesis — it is the geometric input of the source, the affine case of
Stacks 09RE read across the comparison of the small étale and the Zariski site — so no
`@[stacks 09RI]` attribute is placed.  That statement is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomPerfectQcohLeaf.lean`, as
`AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite`,
which discharges the hypothesis `hunit` of the last theorem below; both clauses of the tag are
proved there.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isColim_of_structureSheafAffineBaseChange_of_qcoh`:
  **clause (1) of Stacks 09RI with the quasi-coherence of `Lu^*K₀` available to the leaf** — the
  conclusion of the tag for `E₀` perfect and `K₀` in `D_QCoh(𝒪_{X₀})`, from a leaf hypothesis
  *weaker* than the one of `isColim_of_structureSheafAffineBaseChange`.
* `AlgebraicGeometry.Space.DescentSituation`
  `.isColim_of_structureSheafAffineBaseChange_of_forall_qcoh`:
  the same conclusion from the leaf statement for the pairs `(𝒪_U, L)` over the affine objects
  étale over `X₀` and *every* quasi-coherent `L` on them — the shape in which the leaf mentions
  neither `K₀` nor the descent situation.
* `AlgebraicGeometry.Space.DescentSituation`
  `.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_qcohUnit`:
  the same weakening of the carried colimit statement one level up, at the tag's own disjunction.
  There it costs **no** hypothesis at all: both disjuncts of `hcase` already contain the
  quasi-coherence of `K₀`, so the binders are exactly those of
  `isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

namespace DescentSituation

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Stacks 09RI, clause (1), reduced to the colimit statement at the structure sheaf with the
quasi-coherence of the second argument available.**  In Situation 09RH let `E₀` be a *perfect*
object of `D(𝒪_{X₀})` and let `K₀` lie in `D_QCoh(𝒪_{X₀})`, as clause (1) of the tag assumes.  If
for every étale `u : U ⟶ X₀` with `U` affine and every `n` the map

`colim_{i ≥ 0} Hom_{D(𝒪_{U_i})}(𝒪_{U_i}, (Lu^*K₀)_i⟦n⟧) ⟶ Hom_{D(𝒪_U)}(𝒪_U, (Lu^*K₀)⟦n⟧)`

is bijective, `U_i = X_i ×_{X₀} U`, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective.

This is `AlgebraicGeometry.Space.DescentSituation.isColim_of_structureSheafAffineBaseChange` with
`Lu^*K₀ ∈ D_QCoh(𝒪_U)` handed to the leaf hypothesis, which is what the source's proof of the
leaf uses and what the hypothesis there has no way to obtain: `K₀` is an arbitrary object in that
statement.  Its own hypothesis `hunit` is therefore *weaker* than the one of
`isColim_of_structureSheafAffineBaseChange`, at the cost of the tag's own assumption `hK₀` on
`K₀`; the quasi-coherence it supplies comes from `hK₀` by Stacks 08F4
(`AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`), which holds for
every morphism of algebraic spaces and in particular for `u`.  The colimit statement at the
structure sheaf is not proved in this file; it is
`AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite`. -/
theorem isColim_of_structureSheafAffineBaseChange_of_qcoh
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hE₀ : (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect E₀)
    (hK₀ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).1 (D.stage D.base).2) n).obj
        K₀).IsQuasicoherentOnSite)
    (hunit : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (_hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS V.1 V.2) n).obj
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)).IsQuasicoherentOnSite) →
        PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
          (smallEtaleDerivedPullbackData B S hS)
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
            (SheafOfModules.unit _))
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  D.isColim_of_structureSheafAffineBaseChange E₀ K₀ hE₀ fun u hu hV =>
    hunit u hu hV (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS u K₀ hK₀)

/-- **Stacks 09RI, clause (1), reduced to the colimit statement at the structure sheaf for the
quasi-coherent second arguments.**  The same conclusion as
`AlgebraicGeometry.Space.DescentSituation.isColim_of_structureSheafAffineBaseChange_of_qcoh`, from
the leaf statement asked for *every* `L ∈ D_QCoh(𝒪_U)` on the affine objects étale over `X₀`
rather than for `Lu^*K₀` alone.

This is the shape in which the leaf is a standalone statement about an affine algebraic space —
it mentions neither `K₀` nor the descent situation — which is the form the geometric input of the
source proves: the affine case of Stacks 09RE read across the comparison of the small étale and
the Zariski site, where quasi-coherence is what puts `L` in the image of `𝒪_U ⊗_A -`. -/
theorem isColim_of_structureSheafAffineBaseChange_of_forall_qcoh
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hE₀ : (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect E₀)
    (hK₀ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).1 (D.stage D.base).2) n).obj
        K₀).IsQuasicoherentOnSite)
    (hunit : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (_hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        ∀ L : derivedModules B S hS V,
          (∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS V.1 V.2) n).obj L).IsQuasicoherentOnSite) →
          PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
            (smallEtaleDerivedPullbackData B S hS)
            ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
              (SheafOfModules.unit _)) L) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  D.isColim_of_structureSheafAffineBaseChange_of_qcoh E₀ K₀ hE₀ hK₀
    fun u hu hV hqc => hunit u hu hV _ hqc

end

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)
  (E₀ K₀ : derivedModules B S hS (D.stage D.base))

/-- **Stacks 09RI with the quasi-coherence of `Lu^*K₀` available to the carried colimit
statement.**  Exactly `AlgebraicGeometry.Space.DescentSituation`
`.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent`,
with the same binders, except that its hypothesis `hunit` — the colimit statement at the
structure sheaf over the affine objects étale over `X₀`, which is what clause (1) still needs —
may now use `Lu^*K₀ ∈ D_QCoh(𝒪_U)`.

Nothing is assumed beyond the tag: both disjuncts of `hcase` contain the quasi-coherence of `K₀`,
and Stacks 08F4
(`AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`) carries it along
`u`.  So this hypothesis is strictly weaker than the one it replaces at no cost, which matters
because the route to the leaf needs quasi-coherence to put the second argument in the image of
`𝒪_U ⊗_A -`, as in
`AlgebraicGeometry.Space.exists_pointTensor_iso_of_isQuasicoherentOnSite_of_isAffineSpace`. -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_qcohUnit
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hunit : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (_hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS V.1 V.2) n).obj
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)).IsQuasicoherentOnSite) →
        PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
          (smallEtaleDerivedPullbackData B S hS)
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
            (SheafOfModules.unit _))
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀))
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
  have hK := hcase.elim (fun h => h.2) fun h => h.2.1
  D.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent E₀ K₀ hI
    (fun u hu hV => hunit u hu hV
      (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS u K₀ hK))
    T hcase

end

end DescentSituation

end AlgebraicGeometry.Space

end
