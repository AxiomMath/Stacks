module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.AcyclicCoveringFamilyLargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts

/-!
# The cohomology of a derived inverse limit on an algebraic space

Let `S` be a scheme of a big fppf site, let `X` be an algebraic space over `S` and let `(K_n)`
be an inverse system in `D_QCoh(𝒪_X)` such that `H^q(K_{n+1}) → H^q(K_n)` is surjective for
every `q ∈ ℤ` and every `n`.  Write `K = R lim K_n` for a derived inverse limit in `D(𝒪_X)`.
[Stacks, Tag 0D3E] asserts three things:

1. `H^q(K) = lim H^q(K_n)`;
2. `R lim H^q(K_n) = lim H^q(K_n)`;
3. `H^p(U, lim H^q(K_n)) = 0` for `p > 0` and `U` an affine open of `X`.

This file states all three with no hypothesis beyond the source's own: quasi-coherence of the
cohomology sheaves and surjectivity of the transition maps between them.

## Main results

* `AlgebraicGeometry.Space.isLimit_cohomology_of_isDerivedLimit_of_epi`: **clause (1)**.
* `AlgebraicGeometry.Space.isDerivedLimit_single_limit_homology_unconditional`: **clause (2)**.
* `AlgebraicGeometry.Space.isZero_cohomology_limit_homology_of_isAffineChart_unconditional`:
  **clause (3)**.
* `AlgebraicGeometry.Space.epi_sectionsFunctor_map_of_isQuasicoherentOnSite`: a surjection of
  quasi-coherent `𝒪_X`-modules is surjective on the sections over an affine étale chart, in the
  shape the site-theoretic criteria ask for it.
* `AlgebraicGeometry.Space.hasProductsOfShape_nat_derivedCategory_modules`: `D(𝒪_X)` has
  countable products, which is what lets clause (1) speak of a derived inverse limit without
  assuming one exists.

## Implementation notes

*The three inputs of the source's proof.*  The source proves clause (1) from Cohomology on
Sites, Lemma [Stacks, Tag 0A09] and clauses (2) and (3) from Cohomology on Sites, Lemma
[Stacks, Tag 0BKY], after checking on the affine objects of `X_étale` that a quasi-coherent
module is acyclic and that a surjection of quasi-coherent modules is surjective on sections.
Each of those three checks is a theorem of this tree:

* that the affine étale charts cover the small étale site, in the index universe
  `CategoryTheory.GrothendieckTopology.HasEnoughObjects` asks for, is
  `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`;
* the acyclicity is `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`
  for module-valued sections, as Tag 0A09 phrases it, and
  `AlgebraicGeometry.Space.isZero_rightDerived_sectionsFunctor_of_isAffineChart` for
  abelian-group-valued sections, as Tag 0BKY phrases it;
* the surjectivity on sections is
  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`, read through
  `AlgebraicGeometry.Space.epi_sectionsFunctor_map_of_isQuasicoherentOnSite` below into the
  epimorphism of abelian groups that Tag 0BKY asks for.

So `AlgebraicGeometry.Space.isDerivedLimit_single_limit_homology` and
`AlgebraicGeometry.Space.isZero_cohomology_limit_homology_of_isAffineChart`, which take those
three as named hypotheses at a free module universe, are applied here at the module universe of
the structure rings with all three supplied.

*The module universe is `u`, the universe of the structure rings.*  That is where the three
inputs live: the acyclicity and the surjectivity both rest on Descent, Proposition
[Stacks, Tag 03DX] (2) for the small étale site of an algebraic space, which this library has
for `AlgebraicGeometry.Space.Modules.{u, u}`.  Grothendieck abelianness of the modules and
enough injectives among them, which the conditional forms take as instance arguments because
they are stated at a free module universe, are
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` and
`AlgebraicGeometry.Space.enoughInjectives_modules` here.

*Clause (1) and the universes of the site.*  The small étale site of an algebraic space has
objects in `Type (u + 1)` and morphisms in `Type u`.  Tag 0A09 is formalized at
`Stacks.Cohomology.DerivedLimitAcyclic.isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover`
for a ringed site whose objects, morphisms and structure rings share one universe.  The same
argument, with the modules at the universe of the structure rings and the objects of the site
free, is `Stacks.Cohomology.DerivedLimitAcyclic.LargeSite.isLimit_cohomology_of_isDerivedLimit`
(with Tag 0BKZ,
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`,
supplied), and clause (1) is its instance.

*How the derived limit is presented.*  As in [Stacks, Tag 0A0J], the scheme-theoretic
counterpart, `L` is a derived limit of `(K_n)` in the sense of
`CategoryTheory.IsDerivedLimit`: the Milnor triangle on the product of the system.  The
conclusion of clause (1) exhibits the limiting cone on the degree-`q` cohomology sheaves, its
legs induced by the projections of such a triangle, rather than merely asserting that the
comparison is invertible.

The product of the system, which is what makes `∏ᶜ` and with it the Milnor triangle and
`CategoryTheory.IsDerivedLimit` expressible at all, is **not** a hypothesis of clause (1): it is
`AlgebraicGeometry.Space.hasProductsOfShape_nat_derivedCategory_modules` below, proved with no
hypothesis and made a local instance, so the statement names no assumption the source does not
make.

*Affine opens and affine charts.*  Clause (3) is stated for every affine object of the small
étale site of `X`.  An affine open of `X` is one, and the source's own proof is about all of
them.

## References

* [Stacks Project, Tag 0D3E](https://stacks.math.columbia.edu/tag/0D3E)
* [Stacks Project, Tag 0A09](https://stacks.math.columbia.edu/tag/0A09)
* [Stacks Project, Tag 0A0J](https://stacks.math.columbia.edu/tag/0A0J)
* [Stacks Project, Tag 0BKY](https://stacks.math.columbia.edu/tag/0BKY)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Instances for the `𝒪_X`-modules at the universe of the structure rings

Grothendieck abelianness and enough injectives are needed while the statements below are being
elaborated, since the right derived functors of sections occur in them, and instance search for
either one stalls on a universe constraint: the library's instances for sheaves of modules
produce a module universe at least that of the objects of the site, which here is `u + 1`.  So
the two theorems are made local instances, as in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedFunctorAmplitudeUnbounded.lean`. -/

attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

/-- **The unbounded derived category of `𝒪_X`-modules has countable products**, at the module
universe of the structure rings and with no hypothesis.

This is what makes the derived inverse limit of a sequential system expressible, so it is proved
here rather than assumed: the exactness of countable products that [Stacks, Tag 07KC] asks for
is not available for these modules, and
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules` wants a module
universe containing the universe `u + 1` of the objects of the site.  What does apply is the
K-injective route
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective`,
whose two inputs are the countable products of the modules themselves,
`AlgebraicGeometry.Space.hasProductsOfShape_nat_modules_ringUniverse`, and the K-injective
resolutions of [Stacks, Tag 079P],
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`. -/
theorem hasProductsOfShape_nat_derivedCategory_modules :
    HasProductsOfShape ℕ (DerivedCategory (Modules.{u, u} B S hS F hF)) := by
  let := hasProductsOfShape_nat_modules_ringUniverse B S hS F hF
  exact Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    (exists_quasiIso_isKInjective_modules B S hS F hF)

attribute [local instance] hasProductsOfShape_nat_derivedCategory_modules

/-- **A surjection of quasi-coherent `𝒪_X`-modules is surjective on the sections over an affine
étale chart**, as an epimorphism of abelian groups.

This is `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`, which is
unconditional, read through `AddCommGrpCat.epi_iff_surjective`: the sections functor of a ringed
site is the evaluation of a sheaf of modules followed by forgetting the module structure, so the
underlying function of its value at a morphism is the morphism's own component. -/
theorem epi_sectionsFunctor_map_of_isQuasicoherentOnSite
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U)
    (M N : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N) (hf : Epi f) :
    Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS F hF) U).map f) :=
  (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_val_app_of_epi_of_isQuasicoherentOnSite (hF := hF) f hf hM hN U hU)

/-- **Stacks Project, Tag 0D3E, clause (1).** Let `S` be a scheme, let `X` be an algebraic space
over `S` and let `(K_n)` be an inverse system in `D_QCoh(𝒪_X)` whose transition maps
`H^q(K_{n+1}) ⟶ H^q(K_n)` on cohomology sheaves are surjective.  If `L` is a derived inverse
limit of the system then `H^q(L) = lim H^q(K_n)`: the cone on the degree-`q` cohomology sheaves
whose legs are induced by the projections of a derived-limit triangle for `L` is a limit cone.

This is Tag 0A09 —
`Stacks.Cohomology.DerivedLimitAcyclic.LargeSite.isLimit_cohomology_of_isDerivedLimit`, its
content with Tag 0BKZ supplied on a site whose objects live above its morphisms — on the small
étale site of `X`, with the source's two checks on the
affine objects of that site discharged: the affine étale charts cover it, and a quasi-coherent
module both is acyclic on an affine chart and receives surjections on its sections there, which
makes each tower of sections Mittag-Leffler and kills its first derived inverse limit. -/
@[stacks 0D3E "clause (1): H^q(R lim K_n) = lim H^q(K_n), as the canonical limiting cone; the \
source's citation 0A09 is applied with its hypotheses on the affine étale charts of the space \
discharged (they cover the small étale site; a quasi-coherent module is acyclic on one; a \
surjection of quasi-coherent modules is surjective on its sections there).  The module universe \
is the universe of the structure rings"]
theorem isLimit_cohomology_of_isDerivedLimit_of_epi
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B S hS F hF))
    (hqc : ∀ (n : ℕ) (q : ℤ), ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (L : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hL : IsDerivedLimit K L) (q : ℤ) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (Modules.{u, u} B S hS F hF))) ∧
      ∃ τ : (Functor.const ℕᵒᵖ).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) q).obj L) ⟶
          K ⋙ DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) q,
        (∀ n : ℕ, τ.app ⟨n⟩ =
          (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) q).map
            (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) :=
  Stacks.Cohomology.DerivedLimitAcyclic.LargeSite.isLimit_cohomology_of_isDerivedLimit
    (smallEtaleRingedSite B S hS F hF) K L hL (IsAffineChart B S hS F)
    (hasEnoughObjects_isAffineChart B S hS F)
    (fun U hU i n ↦ isZero_rightDerived_evaluation_of_isAffineChart
      B S hS F hF _ (hqc n i) U hU)
    (fun U hU i ↦ isZero_firstDerivedLimit_sectionsSystem_of_isAffineChart
      B S hS F hF K i (fun n ↦ hqc n i) (fun n ↦ hsurj n i)
      (epi_sectionsFunctor_map_of_isQuasicoherentOnSite B S hS F hF) U hU)
    q

/-- **Stacks Project, Tag 0D3E, clause (2).** Under the same hypotheses,
`R lim H^q(K_n) = lim H^q(K_n)`: the ordinary inverse limit of the degree-`q` cohomology
sheaves, placed in degree zero, is a derived inverse limit of the system of those sheaves.

This is `AlgebraicGeometry.Space.isDerivedLimit_single_limit_homology` with its three named
hypotheses supplied: `hcover` by
`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`, `h03DWab` by
`AlgebraicGeometry.Space.isZero_rightDerived_sectionsFunctor_of_isAffineChart` and `h03DWepi` by
`AlgebraicGeometry.Space.epi_sectionsFunctor_map_of_isQuasicoherentOnSite`. -/
@[stacks 0D3E "clause (2): R lim H^q(K_n) = lim H^q(K_n); the source's citations are applied \
with their hypotheses on the affine étale charts of the space discharged (they cover the small \
étale site; a quasi-coherent module is acyclic on one; a surjection of quasi-coherent modules \
is surjective on its sections there).  The module universe is the universe of the structure \
rings"]
theorem isDerivedLimit_single_limit_homology_unconditional
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B S hS F hF))
    (hqc : ∀ (n : ℕ) (q : ℤ), ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (q : ℤ) :
    ∃ h : HasProduct (fun n : ℕ =>
        ((K ⋙ DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) q) ⋙
          DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (Modules.{u, u} B S hS F hF)) _ _ _ _ _ _
        ((K ⋙ DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) q) ⋙
          DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0) h
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj
          (limit (K ⋙ DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS F hF) q))) :=
  isDerivedLimit_single_limit_homology B S hS F hF K hqc hsurj
    (hasEnoughObjects_isAffineChart B S hS F)
    (fun U hU M hM ↦
      isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS F hF M hM U hU)
    (epi_sectionsFunctor_map_of_isQuasicoherentOnSite B S hS F hF)
    q

/-- **Stacks Project, Tag 0D3E, clause (3).** Under the same hypotheses, for every affine étale
chart `U` of `X` and every `p > 0` we have `H^p(U, lim H^q(K_n)) = 0`.

This is `AlgebraicGeometry.Space.isZero_cohomology_limit_homology_of_isAffineChart` with its
three named hypotheses supplied, exactly as in
`AlgebraicGeometry.Space.isDerivedLimit_single_limit_homology_unconditional`.  The source states
the vanishing for an affine open of `X`; every affine open is an affine object of the small
étale site, and the statement is given for all of them, as the source's own proof is. -/
@[stacks 0D3E "clause (3): H^p(U, lim H^q(K_n)) = 0 for p > 0 and U an affine étale chart; the \
source's citations are applied with their hypotheses on the affine étale charts of the space \
discharged (they cover the small étale site; a quasi-coherent module is acyclic on one; a \
surjection of quasi-coherent modules is surjective on its sections there).  The module universe \
is the universe of the structure rings"]
theorem isZero_cohomology_limit_homology_of_isAffineChart_unconditional
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B S hS F hF))
    (hqc : ∀ (n : ℕ) (q : ℤ), ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (q : ℤ) (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS F hF) U).rightDerived p).obj
      (limit (K ⋙ DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS F hF) q))) :=
  isZero_cohomology_limit_homology_of_isAffineChart B S hS F hF K hqc hsurj
    (hasEnoughObjects_isAffineChart B S hS F)
    (fun V hV M hM ↦
      isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS F hF M hM V hV)
    (epi_sectionsFunctor_map_of_isQuasicoherentOnSite B S hS F hF)
    q U hU p hp

end AlgebraicGeometry.Space

end
