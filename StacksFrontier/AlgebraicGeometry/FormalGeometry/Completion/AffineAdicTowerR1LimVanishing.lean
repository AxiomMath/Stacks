module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineEdgeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineSectionsSiteComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CoherentCompletionAffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAdicCompletionMittagLeffler
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicDualDegreeZero

/-!
# `lim_n H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ) ≅ H^q(U, K^∧)` over an open of a scheme

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals, `K` an
object of `D(𝒪_X)` and `U ⊂ X` an open. Part (1) of [Stacks, Tag 0A0K] presents `K^∧` as a
derived limit of the adic reduction tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, through the canonical
factorizations `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of [Stacks, Tag 0CQH].
This file carries that presentation across `RΓ(U, -)` and reads off its degree-`q` cohomology:
the comparison

`c : H^q(U, K^∧) ⟶ lim_n H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)`,

pinned by `c ≫ limⁿ = H^q(RΓ(U, K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹))`, is invertible as soon as the
degree-`(q - 1)` tower `n ↦ H^{q-1}(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` is Mittag-Leffler. That is the
affine-local comparison named in `Completion/CohomologyAffineAdicComparison.lean` as one of the
two steps still missing between the canonical comparison proved there and part (2) of
[Stacks, Tag 0A0K].

## Main results

* `Stacks.Algebraization.isMittagLefflerCategorical_of_forall_exists_range_le` — an
  eventual-domination criterion for the Mittag-Leffler condition of [Stacks, Tag 02N0].
* `Stacks.Algebraization.isMittagLefflerCategorical_of_isMittagLeffler_forget` — the converse of
  `isMittagLeffler_forget_of_isMittagLefflerCategorical`: for an inverse system of modules the
  subobject-valued Mittag-Leffler condition is implied by the one on underlying sets.
* `Stacks.Algebraization.isDerivedLimitWithProjections_map_rightDerivedFunctor` — a right derived
  functor carries a derived limit *with its projections* to one, the new projections being the
  images of the old. This is [Stacks, Tag 08U1] refined so that the cone survives.
* `Stacks.Algebraization.isDerivedLimitWithProjections_adicReductionTower_derivedCompletion` and
  `Stacks.Algebraization.isDerivedLimitWithProjections_adicReductionTower_generatedIdealSheaf` —
  part (1) of [Stacks, Tag 0A0K] read at the reflector, with the canonical factorizations of
  [Stacks, Tag 0CQH] themselves as projections.
* `Stacks.Algebraization.exists_isIso_comp_limit_homology_derivedSections` — the comparison
  `H^q(U, L) ⟶ lim_n H^q(U, Tₙ)` is invertible for any tower `T` in `D(𝒪_X)` with a
  derived-limit presentation at `L`, granted the Mittag-Leffler condition one degree below.
* `Stacks.Algebraization.isZero_firstDerivedLimit_homology_adicReductionSectionsTower` — the
  `R¹lim` of the cohomology of the adic reduction tower over `U` vanishes.
* `Stacks.Algebraization.exists_isIso_comp_limit_homology_adicReductionSectionsTower` — the
  displayed comparison at the adic reduction tower and the derived completion.
* `Stacks.Algebraization.homologyDerivedSectionsTowerIsoOfIsAffineOpen` — over an affine open,
  the tower `n ↦ H^q(U, Tₙ)` is the tower `n ↦ Γ(U, H^q(Tₙ))`, through the edge morphism of
  [Stacks, Tag 0BKT]; and
  `Stacks.Algebraization.isMittagLefflerCategorical_homology_derivedSections_of_isAffineOpen`,
  the Mittag-Leffler condition transported along it.
* `Stacks.Algebraization.exists_isIso_comp_limit_sections_homology_of_isAffineOpen` and its
  specialization `exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isAffineOpen`
  — the comparison with its target rewritten as `lim_n Γ(U, H^q(Tₙ))`, and its composite with
  each limit projection identified as the edge morphism at `K^∧` followed by
  `Γ(U, H^q(K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹))`. This is the form in which both sides are sheaf-level data
  on `U`, which is what the gluing step of part (2) of [Stacks, Tag 0A0K] consumes.

## Was this a corollary of `Completion/CohomologyAdicCompletionMittagLeffler.lean`?

Half of it, and the other half not at all.

* The **`R¹lim` vanishing itself is a corollary**, and is proved as one:
  `isZero_firstDerivedLimit_homology_adicReductionSectionsTower` is
  `Stacks.Algebraization.isZero_firstDerivedLimit_of_isMittagLefflerCategorical` applied to the
  tower `n ↦ H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)`. That lemma is already stated for an arbitrary tower of
  modules, so nothing had to be redone.
* The **comparison isomorphism is not**.
  `Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler`, the other
  result of that file, is about a different tower in a different vocabulary: a *coherent sheaf*
  `ℱ` and its sheaf-level quotients `ℱ/𝓘ⁿℱ`, with `RΓ` taken over a morphism
  `f : X ⟶ Spec A` through `derivedGlobalSectionsOver`. Here the tower is the *derived* tensor
  `K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of an arbitrary object of `D(𝒪_X)`, and `RΓ` is taken over an open `U`.
  Neither tower is an instance of the other. What is shared is the mechanism, and the pieces of
  it are reused rather than rebuilt: the Milnor sequence of
  `DerivedCategory.exists_milnor_shortExact_of_distTriang` and the vanishing above, packaged for
  `D(ModuleCat A)` by
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π`.

## The two hypotheses, and why they are hypotheses

`exists_isIso_comp_limit_homology_adicReductionSectionsTower` assumes

* `hlim`, part (1) of [Stacks, Tag 0A0K] for `K` over `ℐ`, in the de-existentialised form
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections` with the projections pinned to the
  canonical factorizations. **This one is discharged** for the sheaf of ideals generated by a
  finite family of global sections, by
  `Stacks.Algebraization.isDerivedLimitWithProjections_adicReductionTower_generatedIdealSheaf`
  below.
  `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_adicReductionTower_completion`
  states part (1) at the Čech completion `(completionFunctor X f).obj K`, with its projections
  carrying `AlgebraicGeometry.RingedSite.reflectorIsoCompletionFunctor`, and
  `Stacks.Algebraization.isDerivedLimitWithProjections_adicReductionTower_derivedCompletion`
  moves it onto the reflector with the factorizations themselves as projections. Nothing is left
  over but part (1)'s own pro-vanishing hypothesis `hpz`. It is kept as a hypothesis of the
  comparison itself because that form applies to any sheaf of ideals and any model of `K^∧` — in
  particular to `idealSheafSiteSubmodule 𝓘` of a quasi-coherent ideal sheaf, where relating `ℐ`
  to a global generating family is a separate question.
* `hML`, the Mittag-Leffler condition of the degree-`(q - 1)` tower. This is where the
  mathematical content of the vanishing sits, and it is *not* discharged, for the same reason
  that `Completion/CohomologyAdicCompletionMittagLeffler.lean` does not discharge its own `hML`.
  On the module side the condition is proved — it is the first conjunct of
  [Stacks, Tag 0EGV],
  `AdicCompletion.pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction`,
  for the tower `n ↦ H^i(M ⊗^𝐋_A A/Iⁿ⁺¹)` of a pseudo-coherent `M` over a Noetherian `A`.
  Transporting it to the tower here needs a comparison
  `RΓ(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ) ≅ RΓ(U, K) ⊗^𝐋_{Γ(X, U)} Γ(X, U)/ℐ(U)ⁿ`, and **no such comparison is in
  the library in any generality**: there is no projection formula exchanging derived sections
  with the derived tensor product. So that is the next gap on this route, and it is a separate
  statement from the one proved here.

A second, smaller obstruction on the same route is resolved here. The tree carries two unrelated
Mittag-Leffler predicates: `IsMittagLefflerCategorical`, stated with subobjects, which every
consumer of the `R¹lim` vanishing uses; and Mathlib's `CategoryTheory.Functor.IsMittagLeffler` on
`F ⋙ forget (ModuleCat A)`, which is the form [Stacks, Tag 0EGV] proves. Only one direction of
the bridge existed, `isMittagLeffler_forget_of_isMittagLefflerCategorical`, namely the one that
is useless for feeding a proved condition into the vanishing.
`isMittagLefflerCategorical_of_isMittagLeffler_forget` supplies the other.

## Implementation notes

The step that was missing from the library is not the Milnor sequence but the *cone*. Every
statement that derived sections commute with derived limits — [Stacks, Tag 08U1] and its
instances `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`,
`Stacks.Cohomology.DerivedSectionsMilnor.isDerivedLimit_map_derivedSectionsOverObject`, and the
others — lands either in the bare `CategoryTheory.Pretriangulated.IsDerivedLimit`, which pins no
cone, or in a raw triangle whose structural map is `RΓ.map p ≫ piComparison RΓ _`. The comparison
`H^q(U, K^∧) ⟶ lim_n H^q(U, Kₙ)` has to be *identified* with `H^q` of the canonical
factorizations, or it says nothing about [Stacks, Tag 0CQH], and that identification is lost the
moment the projections are dropped.
`isDerivedLimitWithProjections_map_rightDerivedFunctor` keeps them: the structural map
`RΓ.map (Pi.lift π) ≫ piComparison RΓ _` is `Pi.lift fun n ↦ RΓ.map (π n)` by `Pi.hom_ext`, so
the image presentation has the images of the projections as its own.

`Stacks.Algebraization.schemeSectionsOver` and `Stacks.Algebraization.schemeDerivedSectionsOver`
of `Completion/AffineSectionsSiteComparison.lean` are what exhibit
`Stacks.Cohomology.HypercohomologyEdge.derivedSections` over an open of a scheme as a right
derived functor of an additive, product-preserving functor; the statements are phrased in the
`derivedSections` spelling, which is the one `Completion/CohomologyAffineAdicComparison.lean` and
`Completion/AffineEdgeQuasicoherent.lean` use.

The comparison itself is stated for an arbitrary open `U`, not only an affine one: nothing in
the `R¹lim` argument needs affineness. Affineness enters only in rewriting the limit through the
edge isomorphism — `Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen` is the
one-object form of `homologyDerivedSectionsTowerIsoOfIsAffineOpen`, and what the tower form adds
is that the identification is natural in the index, so that it moves both the Mittag-Leffler
condition and the inverse limit — and in making `hML` available at all.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite
open Stacks.Cohomology.HypercohomologyEdge (derivedSections homotopySections hypercohomologyEdge)
open Stacks.SheafOfModules (opensRingedSite)
open AlgebraicGeometry.RingedSite (adicReductionTower derivedCompletion derivedCompletionAdicFactor)

universe w w₁ w₂ v₁ v₂ u₁ u₂ u

namespace Stacks.Algebraization

section MittagLeffler

/-- **An eventual-domination criterion for the Mittag-Leffler condition.** If for every `i`
there is a `c ≥ i` whose transition map into `F.obj (op i)` has range contained in the range of
*every* transition map into `F.obj (op i)`, then `F` satisfies the Mittag-Leffler condition of
[Stacks, Tag 02N0].

Only the containment is assumed, in the shape in which an eventual-range statement supplies it;
the reverse containment for `k ≥ c` is automatic, because the transition map from `k` factors
through the one from `c`. -/
public theorem isMittagLefflerCategorical_of_forall_exists_range_le {A : Type u₁} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v₁} A)
    (h : ∀ i : ℕ, ∃ c : ℕ, ∃ hic : i ≤ c, ∀ k : ℕ, ∀ hik : i ≤ k,
      LinearMap.range (F.map (homOfLE hic).op).hom ≤
        LinearMap.range (F.map (homOfLE hik).op).hom) :
    IsMittagLefflerCategorical F := by
  refine isMittagLefflerCategorical_of_forall_exists_range_eq F fun i ↦ ?_
  obtain ⟨c, hic, hdom⟩ := h i
  refine ⟨c, hic, fun k hck ↦ le_antisymm ?_ (hdom k (hic.trans hck))⟩
  have hcomp : F.map (homOfLE (hic.trans hck)).op =
      F.map (homOfLE hck).op ≫ F.map (homOfLE hic).op := by
    rw [← F.map_comp]
    congr 1
  intro x hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨(F.map (homOfLE hck).op).hom y, by
    rw [← hy, hcomp]
    rfl⟩

/-- **The Mittag-Leffler condition of an inverse system of modules is detected on underlying
sets.** If the system of sets underlying `F` satisfies Mathlib's
`CategoryTheory.Functor.IsMittagLeffler`, then `F` satisfies the subobject-valued condition of
[Stacks, Tag 02N0].

This is the converse of `isMittagLeffler_forget_of_isMittagLefflerCategorical`, and it is the
direction a consumer of the `R¹lim` vanishing needs: the vanishing is stated for
`IsMittagLefflerCategorical`, while the Mittag-Leffler halves of
[Stacks, Tag 0EGV] and of the pseudo-coherence material are proved for the underlying sets. The
hypothesis gives, at each `op i`, one transition map whose range is contained in the range of
every other, which is exactly the eventual domination of
`isMittagLefflerCategorical_of_forall_exists_range_le`. -/
public theorem isMittagLefflerCategorical_of_isMittagLeffler_forget {A : Type u₁} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v₁} A)
    (hF : (F ⋙ forget (ModuleCat.{v₁} A)).IsMittagLeffler) :
    IsMittagLefflerCategorical F := by
  refine isMittagLefflerCategorical_of_forall_exists_range_le F fun i ↦ ?_
  obtain ⟨j, f, hj⟩ := hF (op i)
  have hic : i ≤ j.unop := leOfHom f.unop
  refine ⟨j.unop, hic, fun k hik ↦ ?_⟩
  have hf : f = (homOfLE hic).op := Subsingleton.elim _ _
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have hmem : x ∈ Set.range ((F ⋙ forget (ModuleCat.{v₁} A)).map f) := by
    refine ⟨y, ?_⟩
    rw [hf]
    exact hy
  obtain ⟨z, hz⟩ := hj (homOfLE hik).op hmem
  exact ⟨z, hz⟩

end MittagLeffler

section RightDerived

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [IsGrothendieckAbelian.{w} A]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]

/-- **A right derived functor carries a derived limit with projections to one, with the images
of the projections as its projections.** This is [Stacks, Tag 08U1],
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`, refined so that the cone survives:
if `π` are the projections of a derived-limit presentation of `T` at `L`, then `RF.map ∘ π` are
the projections of one of `T ⋙ RF` at `RF.obj L`.

Tag 08U1 produces the triangle with structural map `RF.map (Pi.lift π) ≫ piComparison RF _`, and
that map is `Pi.lift fun n ↦ RF.map (π n)`: the two agree after composing with each product
projection, by `piComparison_comp_π` and `Pi.lift_π`. The refinement is what the consumers need,
because the comparison map out of `H^q(RF.obj L)` is only pinned down by its composites with the
limit projections, and those are `H^q(RF.map (π n))` precisely when the cone is kept. -/
public theorem isDerivedLimitWithProjections_map_rightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (T : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    (L : DerivedCategory A) (π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩)
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections T L π) :
    ∃ h : HasProduct fun n : ℕ ↦ (T ⋙ RF).obj ⟨n⟩,
      letI := h
      NoetherianAdicCompletion.IsDerivedLimitWithProjections (T ⋙ RF) (RF.obj L)
        (fun n : ℕ ↦ RF.map (π n)) := by
  obtain ⟨δ, hT⟩ := hL
  obtain ⟨h, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α T L
    (Pi.lift π) ⟨δ, hT⟩
  have hfst : RF.map (Pi.lift π) ≫ piComparison RF (fun n : ℕ ↦ T.obj ⟨n⟩) =
      Pi.lift fun n : ℕ ↦ RF.map (π n) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, piComparison_comp_π, ← RF.map_comp]
    simp
  exact ⟨h, δ', hfst ▸ hT'⟩

end RightDerived

section Reflector

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (I : _root_.SheafOfModules.Submodule
    (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  [(ObjectProperty.ι
    (AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- The derived category of sheaves of modules over the ring sheaf of `X` has products indexed
by `ℕ`. -/
local instance hasProductsOfShape_nat_derivedCategory_reflector :
    HasProductsOfShape ℕ
      (DerivedCategory (_root_.SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

/-- **Part (1) of [Stacks, Tag 0A0K] read at the reflector, from any model of `K^∧`.** The
de-existentialised part (1) available in the library,
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_adicReductionTower_completion`,
presents the Čech completion `(completionFunctor X f).obj K` as the derived limit, with
projections the canonical factorizations of [Stacks, Tag 0CQH] precomposed with
`AlgebraicGeometry.RingedSite.reflectorIsoCompletionFunctor`. This moves that presentation onto
the reflector `(derivedCompletion X I).obj K` with the factorizations themselves as projections,
which is the hypothesis `hlim` of
`Stacks.Algebraization.exists_isIso_comp_limit_homology_adicReductionSectionsTower`.

The content is `NoetherianAdicCompletion.IsDerivedLimitWithProjections.of_iso` together with the
cancellation `e.hom ≫ e.inv ≫ - = -`; it is recorded because the two spellings of `K^∧` differ
and the comparison that part (2) needs is pinned to the factorizations. -/
public theorem isDerivedLimitWithProjections_adicReductionTower_derivedCompletion
    (K : DerivedCategory
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {L : DerivedCategory
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (e : (AlgebraicGeometry.RingedSite.derivedCompletion X I).obj K ≅ L)
    (h : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (AlgebraicGeometry.RingedSite.adicReductionTower X I K) L
      (fun n : ℕ ↦ e.inv ≫
        AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor X I K (n + 1))) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (AlgebraicGeometry.RingedSite.adicReductionTower X I K)
      ((AlgebraicGeometry.RingedSite.derivedCompletion X I).obj K)
      (fun n : ℕ ↦ AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor X I K (n + 1)) := by
  have hfam : (fun n : ℕ ↦
        AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor X I K (n + 1)) =
      fun n : ℕ ↦ e.hom ≫ e.inv ≫
        AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor X I K (n + 1) :=
    funext fun n ↦ (e.hom_inv_id_assoc _).symm
  exact hfam ▸ NoetherianAdicCompletion.IsDerivedLimitWithProjections.of_iso h e

end Reflector

section KoszulPartOne

open MonoidalCategory AlgebraicGeometry.RingedSite
open scoped IsMulCommutative

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat
  isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Part (1) of [Stacks, Tag 0A0K] in the form the comparison of this file consumes.** For the
sheaf of ideals generated by a finite family of global sections, the reflector
`(derivedCompletion X ℐ).obj K` is a derived limit of the adic reduction tower through the
canonical factorizations of [Stacks, Tag 0CQH] themselves — no identification left over.

This is
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_adicReductionTower_completion`, whose
limit object is the Čech completion and whose projections carry
`AlgebraicGeometry.RingedSite.reflectorIsoCompletionFunctor`, moved onto the reflector by
`Stacks.Algebraization.isDerivedLimitWithProjections_adicReductionTower_derivedCompletion`. The
pro-vanishing `hpz` is the only hypothesis, exactly as there. -/
public theorem isDerivedLimitWithProjections_adicReductionTower_generatedIdealSheaf
    (K : DerivedCategory (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (adicReductionTower X (generatedIdealSheaf f) K).obj (op n)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower X (generatedIdealSheaf f) K)
      ((derivedCompletion X (generatedIdealSheaf f)).obj K)
      (fun n : ℕ ↦ derivedCompletionAdicFactor X (generatedIdealSheaf f) K (n + 1)) :=
  isDerivedLimitWithProjections_adicReductionTower_derivedCompletion X _ K
    (reflectorIsoCompletionFunctor X f K)
    (isDerivedLimitWithProjections_adicReductionTower_completion X f K hpz)

end KoszulPartOne

section Scheme

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The comparison `H^q(U, L) ⟶ lim_n H^q(U, Tₙ)` over an open of a scheme is invertible on a
Mittag-Leffler tower.** Let `T` be an inverse system in `D(𝒪_X)` with a derived-limit
presentation at `L` through the projections `π`, and let `U ⊂ X` be open. If the tower
`n ↦ H^{q-1}(U, Tₙ)` of `Γ(X, U)`-modules is Mittag-Leffler, there is a comparison

`c : H^q(U, L) ⟶ lim_n H^q(U, Tₙ)`

with `c ≫ limit.π _ (op n) = H^q(RΓ(U, π n))` for every `n`, and it is an isomorphism.

`RΓ(U, -)` is a right derived functor of evaluation at `U`, which is additive and preserves
countable products, so `isDerivedLimitWithProjections_map_rightDerivedFunctor` transports the
presentation to `D(Γ(X, U))` with the images of `π` as projections; the conclusion is then
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π`, whose
`R¹lim` term vanishes by the Mittag-Leffler condition. No affineness is used. -/
public theorem exists_isIso_comp_limit_homology_derivedSections
    (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩)
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections T L π) (q : ℤ)
    (hML : IsMittagLefflerCategorical
      ((T ⋙ derivedSections (structureSheafRing X.toRingedSpace) U) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) (q - 1))) :
    ∃ c : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q).obj
          ((derivedSections (structureSheafRing X.toRingedSpace) U).obj L) ⟶
        limit ((T ⋙ derivedSections (structureSheafRing X.toRingedSpace) U) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q),
      IsIso c ∧ ∀ n : ℕ,
        c ≫ limit.π ((T ⋙ derivedSections (structureSheafRing X.toRingedSpace) U) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q) (op n) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q).map
            ((derivedSections (structureSheafRing X.toRingedSpace) U).map (π n)) := by
  have : PreservesLimitsOfShape (Discrete ℕ) (schemeSectionsOver U) :=
    _root_.SheafOfModules.evaluationPreservesLimitsOfShape.{u}
      (R := structureSheafRing X.toRingedSpace) (D := Discrete ℕ) (op U)
  obtain ⟨h, hL'⟩ := isDerivedLimitWithProjections_map_rightDerivedFunctor
    (schemeSectionsOver U) (schemeDerivedSectionsOver U) (schemeDerivedSectionsOverUnit U)
    T L π hL
  let := h
  exact NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π
    Γ(X, U) _ _ _ hL' q hML

end Scheme

section AffineEdge

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The hypercohomology edge morphism is invertible on a whole tower, over an affine open.**
If every cohomology sheaf of every term of the tower `T` is quasi-coherent, then whiskering the
edge morphism of [Stacks, Tag 0BKT] with `T` gives an isomorphism of inverse systems: an
isomorphism is a natural transformation all of whose components are invertible, and each
component is `Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen` at one term. -/
public theorem isIso_whiskerLeft_hypercohomologyEdge_of_isAffineOpen
    (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj (T.obj n)).IsQuasicoherent)
    (U : X.affineOpens) (q : ℤ) :
    IsIso (Functor.whiskerLeft T
      (hypercohomologyEdge (structureSheafRing X.toRingedSpace) U.1 q)) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun n ↦
    Stacks.Cohomology.AcyclicOpen.isIso_hypercohomologyEdge_app_of_isBasis X.toRingedSpace
      (T.obj n) X.affineOpens X.isBasis_affineOpens
      (isZero_rightDerived_evaluation_homology_of_isQuasicoherent X (T.obj n) (hqc n)) U.1 U.2 q

/-- **The tower `n ↦ H^q(U, Tₙ)` of hypercohomology modules over an affine open is the tower
`n ↦ Γ(U, H^q(Tₙ))` of sections of the cohomology sheaves**, through the edge morphism. This is
what makes the target of the comparison of
`Stacks.Algebraization.exists_isIso_comp_limit_homology_derivedSections` computable over an
affine open, and it is why the route to part (2) of [Stacks, Tag 0A0K] runs through the adic
reduction tower rather than through `K^∧`: the tower's terms have quasi-coherent cohomology
sheaves by [Stacks, Tag 08DX], and `K^∧` need not. -/
public def homologyDerivedSectionsTowerIsoOfIsAffineOpen (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj (T.obj n)).IsQuasicoherent)
    (U : X.affineOpens) (q : ℤ) :
    T ⋙ derivedSections (structureSheafRing X.toRingedSpace) U.1 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op U.1))) q ≅
      T ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q ⋙
        _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U.1) :=
  @asIso _ _ _ _ (Functor.whiskerLeft T
      (hypercohomologyEdge (structureSheafRing X.toRingedSpace) U.1 q))
    (isIso_whiskerLeft_hypercohomologyEdge_of_isAffineOpen T hqc U q)

/-- The components of `Stacks.Algebraization.homologyDerivedSectionsTowerIsoOfIsAffineOpen` are
the edge morphisms at the terms of the tower. -/
public theorem homologyDerivedSectionsTowerIsoOfIsAffineOpen_hom_app
    (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj (T.obj n)).IsQuasicoherent)
    (U : X.affineOpens) (q : ℤ) (n : ℕᵒᵖ) :
    (homologyDerivedSectionsTowerIsoOfIsAffineOpen T hqc U q).hom.app n =
      (hypercohomologyEdge (structureSheafRing X.toRingedSpace) U.1 q).app (T.obj n) :=
  rfl

/-- **Mittag-Leffler for the tower of cohomology sheaves read on an affine open gives
Mittag-Leffler for the tower of hypercohomology modules.** The two towers are identified by
`Stacks.Algebraization.homologyDerivedSectionsTowerIsoOfIsAffineOpen`, and the Mittag-Leffler
condition of [Stacks, Tag 02N0] depends only on the isomorphism class of an inverse system. -/
public theorem isMittagLefflerCategorical_homology_derivedSections_of_isAffineOpen
    (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj (T.obj n)).IsQuasicoherent)
    (U : X.affineOpens) (q : ℤ)
    (hML : IsMittagLefflerCategorical (T ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
      _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U.1))) :
    IsMittagLefflerCategorical ((T ⋙ derivedSections (structureSheafRing X.toRingedSpace) U.1) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q) :=
  IsMittagLefflerCategorical.of_natIso
    (homologyDerivedSectionsTowerIsoOfIsAffineOpen T hqc U q) hML

/-- **`H^q(U, L) ≅ lim_n Γ(U, H^q(Tₙ))` over an affine open.** Let `T` be an inverse system in
`D(𝒪_X)` whose terms all have quasi-coherent cohomology sheaves, with a derived-limit
presentation at `L` through the projections `π`, and let `U` be an affine open. If the tower
`n ↦ Γ(U, H^{q-1}(Tₙ))` is Mittag-Leffler, there is a comparison

`c : H^q(U, L) ⟶ lim_n Γ(U, H^q(Tₙ))`

with `c ≫ limit.π _ (op n)` the edge morphism at `L` followed by `Γ(U, H^q(π n))`, and it is an
isomorphism.

This is `Stacks.Algebraization.exists_isIso_comp_limit_homology_derivedSections` with its target
rewritten through the edge isomorphism of
`Stacks.Algebraization.homologyDerivedSectionsTowerIsoOfIsAffineOpen`; the description of
`c ≫ limit.π` is the naturality of the edge morphism at `π n`. Both the comparison and its
characterization are now in sheaf-level data on `U`, which is the form the gluing step of part
(2) of [Stacks, Tag 0A0K] consumes. -/
public theorem exists_isIso_comp_limit_sections_homology_of_isAffineOpen
    (T : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩)
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections T L π)
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj (T.obj n)).IsQuasicoherent)
    (U : X.affineOpens) (q : ℤ)
    (hML : IsMittagLefflerCategorical (T ⋙
      DerivedCategory.homologyFunctor X.Modules (q - 1) ⋙
        _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U.1))) :
    ∃ c : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
          ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj L) ⟶
        limit (T ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
          _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U.1)),
      IsIso c ∧ ∀ n : ℕ,
        c ≫ limit.π (T ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
            _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U.1))
            (op n) =
          (hypercohomologyEdge (structureSheafRing X.toRingedSpace) U.1 q).app L ≫
            (_root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
              (op U.1)).map ((DerivedCategory.homologyFunctor X.Modules q).map (π n)) := by
  obtain ⟨c₀, hiso, hc₀⟩ := exists_isIso_comp_limit_homology_derivedSections U T L π hL q
    (isMittagLefflerCategorical_homology_derivedSections_of_isAffineOpen T hqc U (q - 1) hML)
  refine ⟨c₀ ≫ (HasLimit.isoOfNatIso
      (homologyDerivedSectionsTowerIsoOfIsAffineOpen T hqc U q)).hom,
    ((@asIso _ _ _ _ c₀ hiso) ≪≫ HasLimit.isoOfNatIso
      (homologyDerivedSectionsTowerIsoOfIsAffineOpen T hqc U q)).isIso_hom, fun n ↦ ?_⟩
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq c₀ (HasLimit.isoOfNatIso_hom_π
    (homologyDerivedSectionsTowerIsoOfIsAffineOpen T hqc U q) (op n))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (hc₀ n) _) ?_
  refine Eq.trans (whisker_eq _
    (homologyDerivedSectionsTowerIsoOfIsAffineOpen_hom_app T hqc U q (op n))) ?_
  exact (hypercohomologyEdge (structureSheafRing X.toRingedSpace) U.1 q).naturality (π n)

end AffineEdge

section AdicTower

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
  (K : DerivedCategory X.Modules) (U : X.Opens)

/-- The derived category of `𝒪_X`-modules has products indexed by `ℕ`. -/
local instance hasProductsOfShape_nat_affineAdicTower :
    HasProductsOfShape ℕ (DerivedCategory X.Modules) :=
  AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u}
    (opensRingedSite X.sheaf)

/-- **The tower `n ↦ RΓ(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)`** of derived sections over `U` of the adic
reduction tower of [Stacks, Tag 0CQH], as an inverse system in `D(Γ(X, U))`. The index is
shifted by one, as it is in `AlgebraicGeometry.RingedSite.adicReductionTower`: level `n` is the
reduction modulo `ℐⁿ⁺¹`. -/
public abbrev adicReductionSectionsTower :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  adicReductionTower (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘) K ⋙
    derivedSections (structureSheafRing X.toRingedSpace) U

omit [IsLocallyNoetherian X] in
/-- **The `R¹lim` of the cohomology of the adic reduction tower over `U` vanishes on a
Mittag-Leffler tower.** In the cokernel model `CompletionSequences.firstDerivedLimit` that the
Milnor sequence uses, the first derived inverse limit of
`n ↦ H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` is zero as soon as that tower is Mittag-Leffler.

This is `Stacks.Algebraization.isZero_firstDerivedLimit_of_isMittagLefflerCategorical` of
`Completion/CohomologyAdicCompletionMittagLeffler.lean` at this tower; that lemma is already
stated for an arbitrary tower of modules, so the vanishing needed no new argument. It is recorded
here because it is the term that the comparison of
`exists_isIso_comp_limit_homology_adicReductionSectionsTower` kills, and a consumer that wants
the vanishing rather than the comparison should cite it. -/
public theorem isZero_firstDerivedLimit_homology_adicReductionSectionsTower (q : ℤ)
    (hML : IsMittagLefflerCategorical (adicReductionSectionsTower 𝓘 K U ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q)) :
    IsZero (CompletionSequences.firstDerivedLimit Γ(X, U)
      (adicReductionSectionsTower 𝓘 K U ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q)) :=
  isZero_firstDerivedLimit_of_isMittagLefflerCategorical _ hML

/-- **`H^q(U, K^∧) ≅ lim_n H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` over an open of a locally Noetherian
scheme.** Granted part (1) of [Stacks, Tag 0A0K] for `K` over `ℐ` — the hypothesis `hlim`, that
`K^∧` is a derived limit of the adic reduction tower through the canonical factorizations
`AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of [Stacks, Tag 0CQH] — and the
Mittag-Leffler condition of the degree-`(q - 1)` tower, the comparison

`c : H^q(U, K^∧) ⟶ lim_n H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)`

characterized by `c ≫ limit.π _ (op n) = H^q(RΓ(U, K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹))` is an isomorphism.

Pinning `c` to the factorizations, rather than asserting an abstract isomorphism, is the point:
the factorizations are natural in `U`, which is what the sheaf statement of part (2) of
[Stacks, Tag 0A0K] consumes, and an unpinned isomorphism carries no compatibility. Neither
hypothesis is discharged here; see the module documentation for what each would need. -/
public theorem exists_isIso_comp_limit_homology_adicReductionSectionsTower
    (hlim : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘) K)
      ((derivedCompletion (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘)).obj K)
      (fun n : ℕ ↦ derivedCompletionAdicFactor (opensRingedSite X.sheaf)
        (idealSheafSiteSubmodule 𝓘) K (n + 1)))
    (q : ℤ)
    (hML : IsMittagLefflerCategorical (adicReductionSectionsTower 𝓘 K U ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) (q - 1))) :
    ∃ c : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q).obj
          ((derivedSections (structureSheafRing X.toRingedSpace) U).obj
            ((derivedCompletion (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘)).obj K)) ⟶
        limit (adicReductionSectionsTower 𝓘 K U ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q),
      IsIso c ∧ ∀ n : ℕ,
        c ≫ limit.π (adicReductionSectionsTower 𝓘 K U ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q) (op n) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) q).map
            ((derivedSections (structureSheafRing X.toRingedSpace) U).map
              (derivedCompletionAdicFactor (opensRingedSite X.sheaf)
                (idealSheafSiteSubmodule 𝓘) K (n + 1))) :=
  exists_isIso_comp_limit_homology_derivedSections U _ _ _ hlim q hML

/-- **`H^q(U, K^∧) ≅ lim_n Γ(U, H^q(K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹))` over an affine open of a locally
Noetherian scheme.** The comparison of
`Stacks.Algebraization.exists_isIso_comp_limit_homology_adicReductionSectionsTower` with its
target read through the edge isomorphism, so that both the limit and the characterization of the
comparison are sheaf-level data on `U`:

`c ≫ limit.π _ (op n)` is the hypercohomology edge morphism at `K^∧` followed by
`Γ(U, H^q(K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹))`.

The quasi-coherence hypothesis `hqc` is [Stacks, Tag 08DX]. It is a hypothesis on the *tower*,
never on `K^∧`, which is the whole reason this route closes where the three routes recorded in
`Completion/CohomologyAffineAdicComparison.lean` do not.

The reason `hqc` is a hypothesis is not that the adic reduction tower is formed with the
ringed-site tensor `Stacks.SheafOfModules.derivedTensorProductFunctor`, nor that the two models
of the derived tensor product are unidentified; the reason is a different one.

* The two models *are* identified:
  `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` is
  `Stacks.SheafOfModules.derivedTensorProductFunctor X ≅`
  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O`, and for a scheme the
  right-hand side is `Stacks.derivedTensor` after unfolding
  `Stacks.Cohomology.TorAmplitude.derTensor`. There is even a precedent instantiating it at a
  ringed space, `Stacks.Cohomology.DerivedKunnethExt.tensorBridge`.
* The form of [Stacks, Tag 08DX] to cite is not
  `Stacks.Duality.isQuasicoherent_homology_derivedTensor`, which is pinned to the locally small
  derived category and takes bundled `quasiCoherentDerivedCategory` objects, but
  `AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor`, which is stated under
  `HasDerivedCategory.standard` — the model this file uses — and takes the quasi-coherence of
  each factor as a hypothesis.

What actually keeps `hqc` a hypothesis is one of the two factors, and not the one it looks like.
[Stacks, Tag 08DX] needs *both* factors in `D_QCoh`.

* The **first** factor costs nothing once `K` is pseudo-coherent:
  `AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent` ([Stacks, Tag 08E5]) turns
  `RingedSpace.IsPseudoCoherent K` into `∀ j, (H^j K).IsQuasicoherent` with no further
  hypothesis, and already at this spelling — see its use in
  `Stacks.Algebraization.finite_homology_derivedSections_of_isPseudoCoherent`. `K` carries no
  hypothesis in *this* section, so a discharge adds pseudo-coherence; it does not have to assume
  quasi-coherence.
* The **second** factor is `Stacks.Sites.adicQuotientModule (idealSheafSiteSubmodule 𝓘) (n + 1)`,
  and it is proved:
  `Stacks.Algebraization.isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule` of
  `Completion/AdicQuotientModuleSiteQuasicoherent.lean`, on a locally Noetherian scheme at an
  arbitrary `Scheme.IdealSheafData` and nothing else.

  **The two spellings do not differ in the *power*.** The site tower does not take
  `Stacks.IdealPowerSheaf.idealPow`, defined by an `sInf` recursion, against the
  `idealPowerMultiple` of `adicQuotientSystem`, so no comparison of those two is needed.
  `Stacks.Sites.adicQuotientModule` takes `Stacks.Sites.idealPow` of
  `CategoryTheory/Sites/Modules/IdealSubsheaf.lean:229`, which is
  `sheafifySubmodule (presheafIdealPow I n)` — the sheafification of the objectwise power.
  `Stacks.IdealPowerSheaf.idealPow` is a *different* declaration, in
  `CategoryTheory/Sites/ClosedImmersion/ConormalAlgebra.lean`, which `adicQuotientModule` never
  touches. No relation between `Stacks.Sites.idealPow` and `idealPowerMultiple` is proved, and
  none is needed here.

  What the proof needs: a quotient of the structure sheaf by a *locally generated*
  submodule is quasi-coherent
  (`Stacks.SheafOfModules.isQuasicoherent_cokernel_toUnit`), so all that is required is local
  generators of `ℐⁿ`, which `SheafOfModules.IsFiniteType` supplies. Propagating finite generation
  from `ℐ` to `ℐⁿ` is an induction over `Stacks.Sites.isFiniteType_idealSmul` through
  `ℐⁿ⁺¹ = ℐ · ℐⁿ`, whose local half is `idealSmul_idealPow_le_idealPow_succ`.

So `hqc` is discharged for pseudo-coherent `K`, by
`Stacks.Algebraization.isQuasicoherent_homology_adicReductionTower_of_isPseudoCoherent` of that
same file, which carries no hypothesis beyond the pseudo-coherence this tag already assumes. It
remains an explicit hypothesis on the statement below so the statement stays usable at a `K` that
is not pseudo-coherent; pass that lemma to discharge it. The discharged form is
`exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isPseudoCoherent`. -/
public theorem exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isAffineOpen
    (V : X.affineOpens)
    (hlim : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘) K)
      ((derivedCompletion (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘)).obj K)
      (fun n : ℕ ↦ derivedCompletionAdicFactor (opensRingedSite X.sheaf)
        (idealSheafSiteSubmodule 𝓘) K (n + 1)))
    (hqc : ∀ (n : ℕᵒᵖ) (p : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules p).obj
        ((adicReductionTower (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule 𝓘) K).obj n)).IsQuasicoherent)
    (q : ℤ)
    (hML : IsMittagLefflerCategorical
      (adicReductionTower (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘) K ⋙
        DerivedCategory.homologyFunctor X.Modules (q - 1) ⋙
          _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op V.1))) :
    ∃ c : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V.1)) q).obj
          ((derivedSections (structureSheafRing X.toRingedSpace) V.1).obj
            ((derivedCompletion (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘)).obj K)) ⟶
        limit (adicReductionTower (opensRingedSite X.sheaf) (idealSheafSiteSubmodule 𝓘) K ⋙
          DerivedCategory.homologyFunctor X.Modules q ⋙
            _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op V.1)),
      IsIso c ∧ ∀ n : ℕ,
        c ≫ limit.π (adicReductionTower (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘) K ⋙
            DerivedCategory.homologyFunctor X.Modules q ⋙
              _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op V.1))
            (op n) =
          (hypercohomologyEdge (structureSheafRing X.toRingedSpace) V.1 q).app
              ((derivedCompletion (opensRingedSite X.sheaf)
                (idealSheafSiteSubmodule 𝓘)).obj K) ≫
            (_root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
              (op V.1)).map ((DerivedCategory.homologyFunctor X.Modules q).map
                (derivedCompletionAdicFactor (opensRingedSite X.sheaf)
                  (idealSheafSiteSubmodule 𝓘) K (n + 1))) :=
  exists_isIso_comp_limit_sections_homology_of_isAffineOpen _ _ _ hlim hqc V q hML

end AdicTower

end Stacks.Algebraization

end
