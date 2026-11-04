module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StrictAdicQuotientTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.MilnorFibreWithProjections

/-!
# The named `R lim` of the adic quotient tower, and the named comparison map into it

The strictification of `StrictAdicQuotientTower.lean` makes the Milnor machinery of
`CategoryTheory/Triangulated/MilnorFibre*.lean` applicable to the adic quotient tower. This file
applies it: for a ringed site `(𝒞, 𝒪)`, a sheaf of ideals `ℐ ⊂ 𝒪` and a K-flat complex `K̃`, it
names

* the object `AlgebraicGeometry.RingedSite.strictAdicMilnorFibre` — the strict Milnor fibre of
  the tower `n ↦ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`, a *formula*, and
* the map `AlgebraicGeometry.RingedSite.strictAdicComparison` out of `K̃` into it, also a
  formula,

and identifies the composites of that map with the projections as the derived reductions
`K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of [Stacks, Tag 0CQH]. Because both are formulas, invertibility of the
comparison map is a local question: that is
`AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall`.

## What this file does NOT claim, and why

It does **not** claim unconditionally that `Q(strictAdicMilnorFibre)` is a derived limit of the
tower. `Stacks.MilnorTower.isDerivedLimitWithProjections_Q_milnorObj` needs
`HasExactLimitsOfShape (Discrete ℕ) A` — the Milnor triangle it transports has
`Q(∏ₙ Kₙ)` in it, and that is a product of the family `n ↦ Q Kₙ` only when `DerivedCategory.Q`
preserves countable products, which is Grothendieck's axiom AB4\* on `A`.

**AB4\* fails for sheaves of modules on a site**: a countable product of epimorphisms of sheaves
need not be an epimorphism. The library says so in several places, among them the module
documentation of `Homology/DerivedCategory/KInjectiveProducts.lean` and of
`Homology/DerivedCategory/InverseSystem/KInjectiveTowerCocone.lean`, and
`HasExactLimitsOfShape (Discrete ℕ) (AlgebraicGeometry.RingedSite.Modules X)` does not
synthesize. Countable products in `D(𝒪)` do exist —
`hasProductsOfShape_nat_derivedCategory_ringSheaf` obtains them from K-injective resolutions
instead — so `CategoryTheory.Pretriangulated.IsDerivedLimit` is well posed, but `Q(∏ Kₙ)` is not
the product.

So `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_Q_strictAdicMilnorFibre` carries
the exactness as a hypothesis. It is not vacuous: a site with enough weakly contractible
objects supplies it, by
`Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat`
([Stacks, Tag 0947]).

Everything else here — the object, the comparison map, the identification of its composites with
the derived reductions, and the locality of its invertibility — is unconditional, because the
Milnor fibre and the comparison map out of a cone are formulas needing only countable products
in the abelian category itself.

## Main definitions

* `AlgebraicGeometry.RingedSite.strictAdicMilnorFibre` — the strict Milnor fibre of the
  strictified adic quotient tower.
* `AlgebraicGeometry.RingedSite.strictAdicComparison` — the canonical map `K̃ ⟶ R lim` out of the
  strict cone.

## Main results

* `AlgebraicGeometry.RingedSite.strictAdicComparison_proj` — the comparison map recovers the
  maps of the strict cone, on the nose.
* `AlgebraicGeometry.RingedSite.Q_strictAdicComparison_proj_comparisonLeft` — in `D(𝒪)` its
  composite with the `n`-th projection, read through the K-flat comparison, is the derived
  reduction `AlgebraicGeometry.RingedSite.adicQuotientReduction`.
* `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall` — **invertibility of
  the comparison map is local.**
* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_Q_strictAdicMilnorFibre` — under
  AB4\* on the sheaves of modules, the comparison map is a comparison map into an actual derived
  limit, through named projections.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u₂ v₂ u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (Kt : CochainComplex (Modules X) ℤ)

/-! ### The object and the comparison map -/

/-- **The strict Milnor fibre of the strictified adic quotient tower**: a named candidate for
`R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`, given by a formula in `K̃` and `ℐ` with nothing chosen.

It is the mapping cocone of the Milnor endomorphism `(kₙ) ↦ (kₙ - kₙ₊₁)` of
`∏ₙ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`; only countable products in the sheaves of modules are needed to
write it down. -/
abbrev strictAdicMilnorFibre : CochainComplex (Modules X) ℤ :=
  Stacks.MilnorTower.milnorObj (strictAdicReductionTower X I Kt)

/-- **The `n`-th projection of the strict Milnor fibre** onto `Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`. -/
abbrev strictAdicProj (n : ℕ) :
    strictAdicMilnorFibre X I Kt ⟶ (strictAdicReductionTower X I Kt).obj ⟨n⟩ :=
  Stacks.MilnorTower.proj (strictAdicReductionTower X I Kt) n

/-- **The canonical comparison map `K̃ ⟶ R lim (K̃ ⊗_𝒪 𝒪/ℐⁿ⁺¹)`**, out of the strict cone of
[Stacks, Tag 0CQH].

This is the map whose invertibility is the content of `K^∧ = R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)` — see
`AlgebraicGeometry.RingedSite.Q_strictAdicComparison_proj_comparisonLeft`, which identifies its
composites with the projections as the derived reductions of `Q K̃`. It is a formula in `K̃`, not
a lift chosen through a triangle, which is what makes
`AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall` possible. -/
def strictAdicComparison : Kt ⟶ strictAdicMilnorFibre X I Kt :=
  (strictAdicAugmentation X I Kt).augmentationMap

/-- **The comparison map recovers the maps of the strict cone, on the nose.** -/
@[reassoc (attr := simp)]
theorem strictAdicComparison_proj (n : ℕ) :
    strictAdicComparison X I Kt ≫ strictAdicProj X I Kt n =
      strictAdicAugmentationApp X I Kt n :=
  (strictAdicAugmentation X I Kt).augmentationMap_proj n

/-! ### The composites in `D(𝒪)` are the derived reductions -/

/-- **In `D(𝒪)` the comparison map followed by the `n`-th projection is, through the K-flat
comparison, the derived reduction** `Q K̃ ⟶ Q K̃ ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`.

This is the statement that the named map of this file is the comparison map of [Stacks, Tag
0CQH] and not some other map into some other object: its composites with the named projections
are the maps of the cone the tag forms, and those are the reductions of `K` itself.

It is stated with the comparison isomorphism on the side of the derived reduction rather than
inverted on the side of the projection, and proved by an `Eq.trans` chain rather than by `rw`:
`(strictAdicReductionTower X I Kt).obj ⟨n⟩` and `Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])` are definitionally
but not reducibly equal, so a goal in which a tactic has brought both spellings together is not
type-correct at `implicit` transparency and no rewrite fires on it. -/
theorem Q_strictAdicComparison_proj_comparisonLeft
    (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) (n : ℕ) :
    adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft Kt
          (strictAdicQuotientObj X I n) hKt).hom =
      DerivedCategory.Q.map (strictAdicComparison X I Kt) ≫
        DerivedCategory.Q.map (strictAdicProj X I Kt n) :=
  (adicQuotientReduction_comp_comparisonLeft X I Kt hKt n).trans
    ((DerivedCategory.Q.map_comp (strictAdicComparison X I Kt)
            (strictAdicProj X I Kt n)).symm.trans
        (congrArg DerivedCategory.Q.map (strictAdicComparison_proj X I Kt n))).symm

/-! ### Invertibility of the comparison map is local -/

/-- **Invertibility of the comparison map `K̃ ⟶ R lim (K̃ ⊗_𝒪 𝒪/ℐⁿ⁺¹)` is a local property.**

Let `Gᵢ : Mod(𝒪) ⥤ Bᵢ` be additive functors preserving the countable products of the tower, and
suppose they jointly detect quasi-isomorphisms out of `K̃`. If the comparison map of each
base-changed tower is a quasi-isomorphism, so is the comparison map itself.

This is `Stacks.MilnorTower.quasiIso_augmentationMap_of_forall` at the strict cone of
`StrictAdicQuotientTower.lean`, and the reason that file exists. The hypothesis needed of each
`Gᵢ` is about the `Gᵢ`-image of the data alone, so taking the `Gᵢ` to be the restrictions to
the members of a cover turns a chart-by-chart hypothesis into a global conclusion. No exactness
of countable products is used anywhere here.

What makes this work, and what no existential presentation of a derived limit can supply, is
that `AlgebraicGeometry.RingedSite.strictAdicComparison` is a formula: a lift of the cone
through a Milnor triangle is determined only up to `Hom(K̃, (∏ₙ Kₙ)⟦-1⟧)`, which does not
vanish, so a chart-by-chart hypothesis about *some* lift says nothing about any global map. -/
theorem quasiIso_strictAdicComparison_of_forall {ι : Type*} {Bs : ι → Type u₂}
    [∀ i, Category.{v₂} (Bs i)] [∀ i, Abelian (Bs i)] [∀ i, HasProductsOfShape ℕ (Bs i)]
    (Gs : ∀ i, Modules X ⥤ Bs i) [∀ i, (Gs i).Additive]
    (hpc : ∀ i, IsIso (Stacks.MilnorTower.towerProductComparison (Gs i)
      (strictAdicReductionTower X I Kt)))
    (hdetect : ∀ f : Kt ⟶ strictAdicMilnorFibre X I Kt,
      (∀ i, QuasiIso (((Gs i).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) → QuasiIso f)
    (hlocal : ∀ i, QuasiIso
      ((strictAdicAugmentation X I Kt).map (Gs i)).augmentationMap) :
    QuasiIso (strictAdicComparison X I Kt) :=
  Stacks.MilnorTower.quasiIso_augmentationMap_of_forall Gs hpc
    (strictAdicAugmentation X I Kt) hdetect hlocal

/-! ### The derived-limit statement, under AB4\* -/

section AB4Star

variable [HasExactLimitsOfShape (Discrete ℕ) (Modules X)]

/-- Countable products in `D(𝒪)` computed as the images of the countable products of cochain
complexes — the form a Milnor triangle presents a derived limit through, and the one
`Stacks.MilnorTower.isDerivedLimitWithProjections_Q_milnorObj` is stated with.

This is `Stacks.DerivedProducts.hasProductsOfShape_nat` and *not*
`AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf`: the latter
obtains countable products in `D(𝒪)` from K-injective resolutions with no exactness hypothesis,
but then `Q(∏ₙ Kₙ)` is not the product. -/
local instance hasProductsOfShape_nat_derivedCategory_modules_ab4Star :
    HasProductsOfShape ℕ (DerivedCategory (Modules X)) :=
  Stacks.DerivedProducts.hasProductsOfShape_nat

/-- **Under AB4\* on the sheaves of modules, the strict Milnor fibre is a derived limit of the
strictified tower through the images of its projections.**

The exactness of countable products is a genuine hypothesis and not an artefact: it is what
makes `Q(∏ₙ Kₙ)` a product of `n ↦ Q Kₙ`, and it **fails** for sheaves of modules on a general
site. A site with enough weakly contractible objects supplies it, by
`Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat`.

The tower here is `strictAdicReductionTower X I Kt ⋙ DerivedCategory.Q`;
`AlgebraicGeometry.RingedSite.strictAdicReductionTowerIso` identifies it with
`AlgebraicGeometry.RingedSite.adicReductionTower` at `Q K̃` when `K̃` is K-flat. -/
theorem isDerivedLimitWithProjections_Q_strictAdicMilnorFibre :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (strictAdicReductionTower X I Kt ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (strictAdicMilnorFibre X I Kt))
      (fun n : ℕ => DerivedCategory.Q.map (strictAdicProj X I Kt n)) :=
  Stacks.MilnorTower.isDerivedLimitWithProjections_Q_milnorObj
    (strictAdicReductionTower X I Kt)
    (Stacks.MilnorTower.isIso_piComparison_Q_of_hasExactLimits _)

/-- **The comparison map is the lift of the cone of derived reductions into that derived
limit.** Both halves of what a consumer with a cone in hand needs: the presentation, and the
named map whose composites with the named projections are the given maps. -/
theorem isDerivedLimitWithProjections_and_Q_strictAdicComparison_proj :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
        (strictAdicReductionTower X I Kt ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (strictAdicMilnorFibre X I Kt))
        (fun n : ℕ => DerivedCategory.Q.map (strictAdicProj X I Kt n)) ∧
      ∀ n : ℕ, DerivedCategory.Q.map (strictAdicComparison X I Kt) ≫
          DerivedCategory.Q.map (strictAdicProj X I Kt n) =
        DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n) :=
  Stacks.MilnorTower.exists_isDerivedLimitWithProjections_augmented
    (strictAdicAugmentation X I Kt)
    (Stacks.MilnorTower.isIso_piComparison_Q_of_hasExactLimits _)

end AB4Star

end AlgebraicGeometry.RingedSite

end
