module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The standard cover of projective space computes its cohomology

The cohomology of projective `n`-space is computed by the Čech complex of its `n + 1` standard
coordinate charts. This file supplies the geometric input that makes that legitimate — every
finite intersection of standard charts is again an affine open — and draws the two consequences
that need nothing further: the canonical comparison from Čech cohomology of the standard cover
to sheaf cohomology is an isomorphism in every degree, and the cohomology of a quasi-coherent
module on projective `n`-space vanishes above degree `n`.

The intersection statement is the first sentence of the proof of
[Stacks, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT): the standard opens `D₊(T_i)` of
`Proj` are closed under intersection, since `D₊(f) ⊓ D₊(g) = D₊(fg)` and a product of
coordinates is again homogeneous of positive degree. The vanishing statement is clause (2) of
[Stacks, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS); as in the source it needs only
that projective space is covered by `n + 1` affine opens and has affine diagonal, so no
Noetherian hypothesis on the base ring appears, and quasi-coherence replaces coherence.

## Main results

* `Stacks.ProjectiveCohomology.iInf_basicOpen_eq_basicOpen_prod`: a finite intersection of
  standard opens of `Proj` is the standard open of the product.
* `Stacks.ProjectiveCohomology.isAffineOpen_iInf_basicOpen_X`: every finite intersection of the
  coordinate standard opens of `Proj R[T₀, …, Tₙ]` is an affine open.
* `Stacks.ProjectiveCohomology.isAffineOpen_iInf_chart`: the same for the charts of projective
  `n`-space over a ring, i.e. the hypothesis of [Stacks, Tag 01XD] for the standard cover.
* `Stacks.ProjectiveCohomology.isIso_cechCohomologyToCohomology_chart`: **the standard cover
  computes the cohomology of projective space.**
* `Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt`: **[Stacks, Tag 01YS], clause (2)** — the
  cohomology of a quasi-coherent module on projective `n`-space vanishes in degrees above `n`.

## Implementation notes

**Two models of projective space, and which statements live on which.** The intersection
lemmas are stated for `Proj` of an arbitrary graded ring, and then for `Proj R[T₀, …, Tₙ]`,
which is the source's definition of `ℙⁿ_R`. The library's `ℙⁿ_R`,
`AlgebraicGeometry.projectiveSpaceOverRing`, is instead the base change of the integral model
`Proj (ULift ℤ)[T₀, …, Tₙ]` along `Spec R ⟶ Spec ℤ`, and the identification of the two is not in
the library. Rather than assume it, the charts of the library's model are taken to be the
preimages of the integral charts; affineness then comes from the integral statement and the fact
that the projection to the integral model is an affine morphism, which is where
`isAffineHom_toIntegralAtUniverse` is used. So nothing here depends on the missing comparison.

**The index type.** [Stacks, Tag 01XD] indexes the covering by a type in the universe of the
scheme, so the cover passed to it is indexed by `ULift (Fin (n + 1))` while the `Fin`-indexed
form is what `Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover` wants. Both
are recorded, and the affineness hypothesis is proved once, in the `Fin`-indexed form.

**The affine diagonal is free.** `Proj` of any graded ring is a separated scheme in Mathlib, and
projective space over a separated base is separated because its structure morphism factors
through the base; `IsAffineHom` of the absolute diagonal is then found by instance search. This
is why clause (2) carries no separatedness hypothesis.

**What is still missing.** The computation of
`H^q(ℙⁿ_R, 𝒪(d))` itself — [Stacks, Tag 01XT] — is not here and is not implied by anything here.
Given this file, what it still needs is: the sections of the twist
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` over a standard open
`D₊(T_{i₀} ⋯ T_{i_p})`, identified with the degree-`d` part of the corresponding localization of
the polynomial ring; the resulting `ℤ^{n+1}`-grading of the ordered Čech complex; the
contracting homotopy for the weights with at least one, but not every, exponent negative; and
the identification of the all-negative weights with the top cohomology. Clause (3) of
[Stacks, Tag 01YS] — finiteness of `H^q(ℙⁿ_R, ℱ)` over a Noetherian `R` for coherent `ℱ`, which
is the base case the dévissage of [Stacks, Tag 02O5] reduces to — needs that computation and is
*not* a consequence of clause (2).

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.CechDerived

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveCohomology

/-! ### Finite intersections of standard opens of `Proj` -/

section Proj

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- An intersection of standard opens of `Proj` over a finite index set is the standard open of
the product. The empty case is included: both sides are then `⊤`, since `D₊(1) = ⊤`. -/
@[ega "II 2.3.3" "more general"]
theorem biInf_basicOpen_eq_basicOpen_prod {ι : Type*} (t : Finset ι) (f : ι → A) :
    (⨅ i ∈ t, Proj.basicOpen 𝒜 (f i)) = Proj.basicOpen 𝒜 (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, ih, Finset.prod_insert ha, Proj.basicOpen_mul]

/-- An intersection of finitely many standard opens of `Proj` is the standard open of the
product of the defining elements. -/
@[ega "II 2.3.3" "more general"]
theorem iInf_basicOpen_eq_basicOpen_prod {ι : Type*} [Fintype ι] (f : ι → A) :
    (⨅ i, Proj.basicOpen 𝒜 (f i)) = Proj.basicOpen 𝒜 (∏ i, f i) := by
  simpa using biInf_basicOpen_eq_basicOpen_prod 𝒜 Finset.univ f

end Proj

/-! ### The charts of `Proj R[T₀, …, Tₙ]` -/

section Polynomial

variable (R : Type u) [CommRing R]

/-- A nonempty product of homogeneous coordinates is homogeneous of positive degree. -/
theorem prod_X_mem_degree {n r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    (∏ k, MvPolynomial.X (s k) : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (r + 1) := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun k => (MvPolynomial.X (s k) : MvPolynomial (Fin (n + 1)) R)) (fun _ => 1)
    (fun k _ => MvPolynomial.isHomogeneous_X R (s k))

/-- **Every finite intersection of the coordinate standard opens of `Proj R[T₀, …, Tₙ]` is an
affine open.** This is the first sentence of the proof of [Stacks, Tag 01XT]: the intersection
is `D₊(T_{i₀} ⋯ T_{i_p})`, and a product of `p + 1` coordinates is homogeneous of degree
`p + 1 > 0`. -/
theorem isAffineOpen_iInf_basicOpen_X {n r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    IsAffineOpen (⨅ k, Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X (s k))) := by
  rw [iInf_basicOpen_eq_basicOpen_prod]
  exact Proj.isAffineOpen_basicOpen _ _ (prod_X_mem_degree R s) (Nat.succ_pos r)

end Polynomial

/-! ### The charts of the library's projective space over a ring -/

section Relative

variable (n : ℕ) (R : CommRingCat.{u})

/-- The projection from projective `n`-space over a ring to the integral model is an affine
morphism: it is the base change of `Spec R ⟶ Spec ℤ` along the integral model. -/
theorem isAffineHom_toIntegralAtUniverse :
    IsAffineHom (projectiveSpaceOver.toIntegralAtUniverse n (Spec R)) :=
  AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback _ _) (isAffineHom_of_isAffine (terminal.from (Spec R)))

/-- The `i`-th standard chart of projective `n`-space over `R`: the preimage of the integral
standard open `D₊(Tᵢ)` under the projection to the integral model. -/
def chart (i : Fin (n + 1)) : (projectiveSpaceOverRing n R).Opens :=
  projectiveSpaceOver.toIntegralAtUniverse n (Spec R) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)

/-- Preimages of opens commute with intersections over a finite index set. -/
theorem preimage_biInf {X Y : Scheme.{u}} (g : X ⟶ Y) {ι : Type*} (t : Finset ι)
    (U : ι → Y.Opens) : g ⁻¹ᵁ (⨅ i ∈ t, U i) = ⨅ i ∈ t, g ⁻¹ᵁ U i := by
  rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
  exact map_finset_inf (Opens.comap g.base.hom) t U

/-- Preimages of opens commute with finite intersections. -/
theorem preimage_iInf {X Y : Scheme.{u}} (g : X ⟶ Y) {ι : Type*} [Finite ι]
    (U : ι → Y.Opens) : g ⁻¹ᵁ (⨅ i, U i) = ⨅ i, g ⁻¹ᵁ U i := by
  cases nonempty_fintype ι
  simpa using preimage_biInf g Finset.univ U

/-- **The standard charts cover projective `n`-space over a ring.** This is the cover of
[Stacks, Tag 01NG], pulled back from the integral model. -/
theorem iSup_chart_eq_top : (⨆ i, chart n R i) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n)

/-- Each standard chart of projective `n`-space over a ring is an affine open. -/
theorem isAffineOpen_chart (i : Fin (n + 1)) : IsAffineOpen (chart n R i) :=
  have := isAffineHom_toIntegralAtUniverse n R
  IsAffineHom.isAffine_preimage _
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) one_pos)

/-- **Every finite intersection of the standard charts of projective `n`-space over a ring is an
affine open** — the hypothesis of [Stacks, Tag 01XD] for the standard cover. -/
theorem isAffineOpen_iInf_chart {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    IsAffineOpen (⨅ k, chart n R (s k)) := by
  have := isAffineHom_toIntegralAtUniverse n R
  have := IsAffineHom.isAffine_preimage (f := projectiveSpaceOver.toIntegralAtUniverse n (Spec R))
    _ (isAffineOpen_iInf_basicOpen_X (ULift.{u} ℤ) s)
  exact (congrArg IsAffineOpen (preimage_iInf _ _)).mp this

/-- The standard cover indexed in the universe of the base ring, as [Stacks, Tag 01XD]
requires. -/
def chartAtUniverse (i : ULift.{u} (Fin (n + 1))) : (projectiveSpaceOverRing n R).Opens :=
  chart n R i.down

/-- The standard charts `chartAtUniverse n R i` cover projective `n`-space over a ring. -/
theorem iSup_chartAtUniverse_eq_top : (⨆ i, chartAtUniverse n R i) = ⊤ := by
  rw [← iSup_chart_eq_top n R]
  exact le_antisymm (iSup_le fun i => le_iSup _ i.down)
    (iSup_le fun i => le_iSup_of_le (ULift.up i) le_rfl)

/-- Every nonempty finite intersection of the charts `chartAtUniverse n R i` is an affine open. -/
theorem isAffineOpen_iInf_chartAtUniverse {r : ℕ} (s : Fin (r + 1) → ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (⨅ k, chartAtUniverse n R (s k)) :=
  isAffineOpen_iInf_chart n R (fun k => (s k).down)

/-- **The Čech complex of the standard cover computes the cohomology of projective space.** For
every quasi-coherent module on projective `n`-space over a ring, the canonical comparison of
[Stacks, Tag 01EQ] from the Čech cohomology of the `n + 1` standard charts to sheaf cohomology
is an isomorphism in every degree. This is [Stacks, Tag 01XD] applied to the standard cover, and
it is the step that turns the computation of [Stacks, Tag 01XT] into a computation with an
explicit complex. -/
theorem isIso_cechCohomologyToCohomology_chart
    (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso ((cechCohomologyToCohomology (projectiveSpaceOverRing n R).ringCatSheaf ⊤
      (chartAtUniverse n R) (iSup_chartAtUniverse_eq_top n R).symm (p : ℤ)).app F) :=
  Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen
    (projectiveSpaceOverRing n R) ⊤ (chartAtUniverse n R)
    (iSup_chartAtUniverse_eq_top n R).symm
    (fun _ s => isAffineOpen_iInf_chartAtUniverse n R s) F p

/-- Projective space over a separated base is separated: its structure morphism factors through
the base, and `Proj` of a graded ring is separated in Mathlib. -/
theorem isSeparated_projectiveSpaceOver (S : Scheme.{u}) [Scheme.IsSeparated S] :
    Scheme.IsSeparated (projectiveSpaceOver n S) := by
  have hP : IsSeparated (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
    dsimp [projectiveSpaceAtUniverse]
    infer_instance
  refine ⟨?_⟩
  have heq : terminal.from (projectiveSpaceOver n S) =
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫
        terminal.from S := terminal.hom_ext _ _
  rw [heq]
  infer_instance

/-- **[Stacks, Tag 01YS], clause (2).** The cohomology of a quasi-coherent module on projective
`n`-space over a ring vanishes in every degree above `n`.

Projective space is covered by its `n + 1` standard charts, all affine, and it is separated,
hence has affine diagonal; [Stacks, Tag 01XI] then bounds the cohomological degree by `n + 1`.
As the source observes, no Noetherian hypothesis is needed, and the conclusion holds for every
quasi-coherent module, not only coherent ones. The source's remaining range `i < 0` is vacuous
in this spelling, where cohomology is indexed by `ℕ`. -/
@[stacks 01YS "clause (2), vanishing above the dimension", ega "III 2.2.2" "(ii), P^n case"]
theorem isZero_Hgroup_of_lt (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent]
    (q : ℕ) (hq : n < q) :
    IsZero (Hgroup (projectiveSpaceOverRing n R).ringCatSheaf ⊤ q F) := by
  have := isSeparated_projectiveSpaceOver n (Spec R)
  have : IsAffineHom
      (pullback.diagonal (terminal.from (projectiveSpaceOverRing n R))) := inferInstance
  exact Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover
    (projectiveSpaceOverRing n R) F (chart n R) (isAffineOpen_chart n R) ⊤
    (iSup_chart_eq_top n R) q (by omega)

end Relative

end Stacks.ProjectiveCohomology

end
