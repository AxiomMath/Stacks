module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseNaturality

/-!
# The weight transition `F_d → F_{kd}`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `Y` a scheme. Section 27.12 attaches to each weight
`d` the set `F_d(Y)` of strict equivalence classes of weight-`d` triples
(`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd`), and the functor `F` of that section is the
colimit of the `F_d` along the transitions attached to divisibility `d ∣ d'`. This file builds
those transitions.

On a triple the transition is the Veronese restriction
`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.veroneseRestrict`: a weight-`d` triple `(L, ψ)` goes
to `(L^{⊗ k}, ψ|_{A^{(kd)}})`, which is a weight-`kd` triple because the tensor power of an
invertible module is invertible and the generation condition is preserved
(`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.iSup_nonvanishingOpen_veroneseRestrict`).

The transition respects strict equivalence, so it descends to the classes: if `β : L ≅ L'` compares
two triples, then `β^{⊗ k}` compares their restrictions.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.DegreeTriple.veronese`: the weight-`kd` triple
  `(L^{⊗ k}, ψ|_{A^{(kd)}})` attached to a weight-`d` triple `(L, ψ)`.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veronese`: the transition
  `F_d(Y) → F_{kd}(Y)` of Section 27.12 attached to the divisibility `d ∣ kd`.

## Main results

* `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.sectionsEquiv_veroneseRestrict`: the Veronese
  restriction respects strict equivalence.

## Implementation notes

The transition is indexed by the cofactor `k`, not by a proof of `d ∣ d'`; a divisibility-indexed
transition is `Fd.veronese` composed with a transport along `d' = k * d`. Since `1 * d` and
`(k' * k) * d` are not definitionally `d` and `k' * (k * d)`, the identity and composition laws of
the colimit diagram are statements about that transport, and are not stated for `Fd.veronese`.

## References

* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (SectionsEquiv)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjVeroneseRestrict

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ} {L L' : Y.Modules}

/-- **The Veronese restriction respects strict equivalence**: if `β : L ≅ L'` carries `ψ` to `ψ'`
degreewise, then its `k`-th tensor power `β^{⊗ k} : L^{⊗ k} ≅ (L')^{⊗ k}` carries the weight-`kd`
restriction of `ψ` to that of `ψ'`. -/
theorem sectionsEquiv_veroneseRestrict {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (k : ℕ) (h : SectionsEquiv 𝒜 ψ ψ') :
    SectionsEquiv 𝒜 (veroneseRestrict 𝒜 ψ k) (veroneseRestrict 𝒜 ψ' k) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨natTensorPowCongr β k, fun m x => ?_⟩
  have hx : ((x : A)) ∈ 𝒜 (k * m * d) := mem_graded_of_eq 𝒜 (by ring) x.2
  rw [veroneseRestrict_toFun, veroneseRestrict_toFun,
    veroneseComp_apply 𝒜 ψ k m x ⟨(x : A), hx⟩ rfl,
    veroneseComp_apply 𝒜 ψ' k m x ⟨(x : A), hx⟩ rfl,
    natTensorPowCongr_app_powVeroneseIso_inv β k m, hβ (k * m) ⟨(x : A), hx⟩]

end Stacks.AlgebraicGeometry.ProjVeroneseRestrict

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (veroneseRestrict
  iSup_nonvanishingOpen_veroneseRestrict sectionsEquiv_veroneseRestrict)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ}

/-- **The weight-`kd` triple attached to a weight-`d` triple `(L, ψ)`**: the invertible module is
the tensor power `L^{⊗ k}` and the graded map is the Veronese restriction of `ψ` to `A^{(kd)}`. -/
def DegreeTriple.veronese (t : DegreeTriple 𝒜 d Y) (k : ℕ) : DegreeTriple 𝒜 (k * d) Y where
  module := natTensorPow t.module k
  isInvertible := haveI := t.isInvertible; inferInstance
  psi := veroneseRestrict 𝒜 t.psi k
  generated := haveI := t.isInvertible
    iSup_nonvanishingOpen_veroneseRestrict 𝒜 t.psi k t.generated

/-- The invertible module of `DegreeTriple.veronese 𝒜 t k` is the tensor power `L^{⊗ k}`. -/
@[simp] theorem DegreeTriple.veronese_module (t : DegreeTriple 𝒜 d Y) (k : ℕ) :
    (DegreeTriple.veronese 𝒜 t k).module = natTensorPow t.module k := rfl

/-- The graded map of `DegreeTriple.veronese 𝒜 t k` is the Veronese restriction of `ψ`. -/
@[simp] theorem DegreeTriple.veronese_psi (t : DegreeTriple 𝒜 d Y) (k : ℕ) :
    (DegreeTriple.veronese 𝒜 t k).psi = veroneseRestrict 𝒜 t.psi k := rfl

/-- **The transition `F_d(Y) → F_{kd}(Y)` of Section 27.12** attached to the divisibility
`d ∣ kd`: the class of a weight-`d` triple goes to the class of the weight-`kd` triple
`(L^{⊗ k}, ψ|_{A^{(kd)}})`. -/
def Fd.veronese (k : ℕ) : Fd 𝒜 d Y → Fd 𝒜 (k * d) Y :=
  Quotient.map (fun t => DegreeTriple.veronese 𝒜 t k) fun _ _ htt' =>
    sectionsEquiv_veroneseRestrict 𝒜 k htt'

/-- `Fd.veronese` sends the class of a triple `t` to the class of `DegreeTriple.veronese 𝒜 t k`. -/
@[simp] theorem Fd.veronese_mk (k : ℕ) (t : DegreeTriple 𝒜 d Y) :
    Fd.veronese 𝒜 k (Fd.mk 𝒜 t) = Fd.mk 𝒜 (DegreeTriple.veronese 𝒜 t k) := rfl

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
