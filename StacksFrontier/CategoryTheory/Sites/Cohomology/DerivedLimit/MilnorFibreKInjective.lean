module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.MilnorFibreWithProjections
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# A named derived limit of a tower, with no exactness of countable products

Let `A` be a Grothendieck abelian category with countable products whose derived category also
has them. Every tower `F : ℕᵒᵖ ⥤ CochainComplex A ℤ` then has a derived limit in `D(A)` presented
by a **formula**: a named object, named projections, and — for a cone on the tower — a named
comparison map. No exactness of the countable products of `A` is assumed anywhere.

That last clause is the point. `Stacks.MilnorTower.isDerivedLimitWithProjections_Q_milnorObj`
presents `Q(milnorObj F)` as a derived limit of `F ⋙ DerivedCategory.Q`, but only after the
product comparison map `Q(∏ₙ Kₙ) ⟶ ∏ₙ Q(Kₙ)` is known to be invertible, and the supplier used
everywhere until now was exactness of the countable products of `A` — Grothendieck's axiom
AB4\*, [Stacks, Tag 07KC]. AB4\* **fails** for sheaves of modules on a site: a countable product
of epimorphisms of sheaves need not be an epimorphism. So on a ringed site that presentation was
unavailable, and with it every argument that needs a derived limit of `D(𝒪)` to be a named
object rather than an object produced by `distinguished_cocone_triangle₁`.

The replacement is [Stacks, Tag 0BK6]: a termwise product of K-injective complexes is
K-injective and computes the product in the derived category
(`Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective`), with no exactness used. It
applies not to `F` but to the levelwise K-injective replacement
`Stacks.MilnorTower.kInjectiveTower A F`, which exists because a Grothendieck abelian category
has a *functorial* K-injective resolution
(`Stacks.Injectives.kInjectiveResolutionFunctor`) — so the replacement is again a tower, and
again a formula in `F`.

## Main definitions

* `Stacks.MilnorTower.kInjectiveTower` — the levelwise K-injective replacement of a tower,
  `F ⋙ Stacks.Injectives.kInjectiveResolutionFunctor A`.
* `Stacks.MilnorTower.kInjectiveTowerInclusion` — the levelwise quasi-isomorphism into it.
* `Stacks.MilnorTower.kInjectiveMilnorObj` — the strict Milnor fibre of the replacement: **the
  named `R lim` of this file.**
* `Stacks.MilnorTower.kInjectiveProj` — its named projections onto the terms of `F`.

## Main results

* `NoetherianAdicCompletion.HasEventualInverses.of_isIso_app` — a natural map of inverse systems
  all of whose components are invertible has eventual inverses, so that the transport lemma
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` applies to
  a natural isomorphism.
* `Stacks.MilnorTower.isIso_piComparison_Q_kInjectiveTower` — the product comparison map of the
  replacement tower is invertible, with no exactness hypothesis.
* `Stacks.MilnorTower.isDerivedLimitWithProjections_Q_kInjectiveMilnorObj` — **the named derived
  limit**: `kInjectiveMilnorObj A F` is a derived limit of `F ⋙ DerivedCategory.Q` through
  `Stacks.MilnorTower.kInjectiveProj`.
* `Stacks.MilnorTower.isDerivedLimit_Q_kInjectiveMilnorObj` — the same as the bare predicate
  `CategoryTheory.Pretriangulated.IsDerivedLimit`.
* `Stacks.MilnorTower.exists_lift_kInjectiveProj` — a cone on `F ⋙ DerivedCategory.Q` factors
  through the projections.

## Implementation notes

The projections of the replacement land in the terms of `kInjectiveTower A F`, not of `F`, so
`Stacks.MilnorTower.kInjectiveProj` corrects them by the inverse of the resolution inclusion,
which is invertible in `D(A)` because the inclusion is a quasi-isomorphism. The presentation is
then transported from the replacement tower to `F ⋙ DerivedCategory.Q` along that natural
isomorphism, by
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`. The
transport is stated for a natural transformation with eventual inverses rather than for a
`InverseSequence.ProIso` precisely because the latter carries a reindexing zig-zag and no
component maps at all, so it cannot say what the transported projections are.

Nothing here is an instance. `Stacks.MilnorTower.kInjectiveTower` is a choice — the chosen
functorial resolution of `Stacks.Injectives.functorialKInjectiveResolution` — and two different
choices give two different named objects. What matters downstream is that a *single* choice is a
formula in `F`, hence commutes with whatever is applied to `F`, which an object produced by
`distinguished_cocone_triangle₁` does not.

No `@[stacks]` attribute is attached. The mathematical content is [Stacks, Tag 0BK6], carried by
`Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective` and by
`Stacks.Injectives.KInjectiveProduct.product_isKInjective`, and [Stacks, Tag 08TC], carried by
`CategoryTheory.Pretriangulated.IsDerivedLimit`; this file only puts them together.

## References

* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe g w v u

namespace NoetherianAdicCompletion

/-- **A natural map of inverse systems whose components are all invertible has eventual
inverses.** At each level take the inverse of that level's component; both composites are the
identity, which is the transition map along `le_refl`.

This is what lets `NoetherianAdicCompletion.IsDerivedLimitWithProjections`
`.comp_of_hasEventualInverses` be used as the transport of a derived-limit presentation along a
natural isomorphism of towers, which is the one case of it where the transported projections are
read off without any reindexing. -/
public theorem HasEventualInverses.of_isIso_app {C : Type u} [Category.{v} C] {F G : ℕᵒᵖ ⥤ C}
    (φ : F ⟶ G) (hφ : ∀ n : ℕ, IsIso (φ.app ⟨n⟩)) : HasEventualInverses φ := fun n => by
  have := hφ n
  refine ⟨n, le_rfl, inv (φ.app ⟨n⟩), ?_, ?_⟩
  · rw [IsIso.hom_inv_id, ← F.map_id]
    exact congrArg F.map (Subsingleton.elim _ _)
  · rw [IsIso.inv_hom_id, ← G.map_id]
    exact congrArg G.map (Subsingleton.elim _ _)

end NoetherianAdicCompletion

namespace Stacks.MilnorTower

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasProductsOfShape ℕ A] [IsGrothendieckAbelian.{g} A]

/-- **The levelwise K-injective replacement of a tower of cochain complexes**: the tower composed
with the chosen functorial K-injective resolution. It is again a tower, and a formula in the
original one. -/
public def kInjectiveTower (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  F ⋙ Stacks.Injectives.kInjectiveResolutionFunctor A

/-- The terms of the replacement tower are K-injective. -/
public instance kInjectiveTower_obj_isKInjective (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕᵒᵖ) :
    ((kInjectiveTower A F).obj n).IsKInjective :=
  Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective A (F.obj n)

/-- **The levelwise quasi-isomorphism of a tower into its K-injective replacement.** Its
naturality square is the naturality square of
`Stacks.Injectives.kInjectiveResolutionInclusion` at the transition map. -/
public def kInjectiveTowerInclusion (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : F ⟶ kInjectiveTower A F where
  app n := (Stacks.Injectives.kInjectiveResolutionInclusion A).app (F.obj n)
  naturality _ _ f := (Stacks.Injectives.kInjectiveResolutionInclusion A).naturality (F.map f)

/-- Each component of the resolution inclusion is a quasi-isomorphism. -/
public instance kInjectiveTowerInclusion_app_quasiIso (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕᵒᵖ) :
    QuasiIso ((kInjectiveTowerInclusion A F).app n) :=
  Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso A (F.obj n)

/-- **The tower and its K-injective replacement become isomorphic in `D(A)`.** Each component
of the resolution inclusion is a quasi-isomorphism, hence invertible after localization, and the
naturality square is the image of the naturality square of the inclusion. -/
public def kInjectiveTowerIso (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    F ⋙ DerivedCategory.Q ≅ kInjectiveTower A F ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun n => asIso (DerivedCategory.Q.map ((kInjectiveTowerInclusion A F).app n)))
    fun {_ _} f => by
      dsimp
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
      exact congrArg DerivedCategory.Q.map ((kInjectiveTowerInclusion A F).naturality f)

/-- **The named `R lim` of a tower of cochain complexes**: the strict Milnor fibre of its
levelwise K-injective replacement. -/
public def kInjectiveMilnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex A ℤ :=
  milnorObj (kInjectiveTower A F)

/-- **The named projections of `Stacks.MilnorTower.kInjectiveMilnorObj` onto the terms of the
original tower**: the Milnor projection of the replacement, corrected by the inverse of the
resolution inclusion. -/
public def kInjectiveProj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (kInjectiveMilnorObj A F) ⟶ (F ⋙ DerivedCategory.Q).obj ⟨n⟩ :=
  DerivedCategory.Q.map (proj (kInjectiveTower A F) n) ≫ (kInjectiveTowerIso A F).inv.app ⟨n⟩

section Products

variable [HasProductsOfShape ℕ (DerivedCategory A)]

/-- **The product comparison map of the K-injective replacement tower is invertible, with no
exactness of countable products assumed.** This is [Stacks, Tag 0BK6]: the termwise product of
the K-injective terms is K-injective, and its image in `D(A)` is the product of their images.

Contrast `Stacks.MilnorTower.isIso_piComparison_Q_of_hasExactLimits`, which gets the same
conclusion for *every* tower out of Grothendieck's axiom AB4\* — a hypothesis unavailable for
sheaves of modules on a site. -/
public theorem isIso_piComparison_Q_kInjectiveTower (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsIso (piComparison DerivedCategory.Q fun k : ℕ => (kInjectiveTower A F).obj ⟨k⟩) :=
  Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective
    (fun k : ℕ => (kInjectiveTower A F).obj ⟨k⟩) fun _ => inferInstance

/-- **The named object is a derived limit of the tower through the named projections, with no
exactness of countable products assumed.**

This is the statement the whole file exists for. Both
`CategoryTheory.Pretriangulated.IsDerivedLimit` and
`NoetherianAdicCompletion.exists_isDerivedLimitWithProjections_of_hasProduct` produce a derived
limit out of
`distinguished_cocone_triangle₁`, whose object is not a formula in the tower and therefore
commutes with nothing; here the object is `Stacks.MilnorTower.kInjectiveMilnorObj A F` and the
projections are `Stacks.MilnorTower.kInjectiveProj A F`, both formulas, and only the connecting
map of the presenting triangle stays existentially quantified. -/
public theorem isDerivedLimitWithProjections_Q_kInjectiveMilnorObj
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (kInjectiveMilnorObj A F)) (kInjectiveProj A F) := by
  have hpres := isDerivedLimitWithProjections_Q_milnorObj (kInjectiveTower A F)
    (isIso_piComparison_Q_kInjectiveTower A F)
  have hev : NoetherianAdicCompletion.HasEventualInverses (kInjectiveTowerIso A F).inv :=
    NoetherianAdicCompletion.HasEventualInverses.of_isIso_app _ fun _ => inferInstance
  exact hpres.comp_of_hasEventualInverses _ hev

/-- **The named object is a derived limit of the tower**, with the projections forgotten. -/
public theorem isDerivedLimit_Q_kInjectiveMilnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsDerivedLimit (F ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (kInjectiveMilnorObj A F)) :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.isDerivedLimit
    (isDerivedLimitWithProjections_Q_kInjectiveMilnorObj A F)

/-- **The named projections form a cone on the tower.** -/
public theorem kInjectiveProj_succ_comp_map (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    kInjectiveProj A F (n + 1) ≫ (F ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op =
      kInjectiveProj A F n :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ
    (isDerivedLimitWithProjections_Q_kInjectiveMilnorObj A F) n

/-- **A cone on the tower factors through the named projections.** The lift is not unique — its
indeterminacy is the obstruction group `Hom(Y, (∏ₙ Tₙ)⟦-1⟧)`, which does not vanish in general —
so a consumer needing a canonical map must pin it by a universal property of `Y` rather than by
this lemma. -/
public theorem exists_lift_kInjectiveProj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    {Y : DerivedCategory A} (c : ∀ n : ℕ, Y ⟶ (F ⋙ DerivedCategory.Q).obj ⟨n⟩)
    (hc : ∀ n : ℕ, c (n + 1) ≫ (F ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op = c n) :
    ∃ v : Y ⟶ DerivedCategory.Q.obj (kInjectiveMilnorObj A F),
      ∀ n : ℕ, v ≫ kInjectiveProj A F n = c n :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_lift
    (isDerivedLimitWithProjections_Q_kInjectiveMilnorObj A F) c hc

end Products

end Stacks.MilnorTower

end
