module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsFlatBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsTensorPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorAnyModel
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.CohomologyAgainstPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitObject
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectTwistsDetectIsomorphisms

/-!
# The restriction of the derived limit to `Xₙ` is `Kₙ`

In Situation [Stacks, Tag 0DIB] let `K` be as in [Stacks, Tag 0DIC], with projections
`πₙ : K ⟶ R(iₙ)_* Kₙ`. The adjoint `cₙ : Liₙ^*K ⟶ Kₙ` of `πₙ` is an isomorphism. This is the input
from which [Stacks, Tag 0DIF] follows by flat base change on a quasi-compact open.

The proof: for every perfect `E` on `X`, [Stacks, Tag 0DID] makes the comparison
`RΓ(X, K ⊗^𝐋 E) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, Kₙ ⊗^𝐋 Liₙ^*E)` an isomorphism, and flat base change makes
`RΓ(X, K ⊗^𝐋 E) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, Liₙ^*(K ⊗^𝐋 E))` one. The first is the second followed by
`RΓ(Xₙ, cₙ ⊗^𝐋 Liₙ^*E)` (the chase
`CategoryTheory.map_adjunction_homEquiv_comp_adjunctionTensorMap` through the projection formula),
so the latter is an isomorphism for every perfect `E`, and
`AlgebraicGeometry.isIso_of_isIso_derivedGlobalSectionsOver_map_derivedTensor` concludes.

## Main results

* `CategoryTheory.map_adjunction_homEquiv_comp_adjunctionTensorMap`: the projection-formula map
  after the tensored adjoint of `c : L K ⟶ M` is the unit followed by `R` of the comparison and
  `c`.
* `StacksDraft.DerivedInverseLimit.isIso_of_isIso_derivedBaseChangeComparison_comp_map`:
  two-out-of-three for base-change comparisons.

## References

* [Stacks Project, Tag 0DIF](https://stacks.math.columbia.edu/tag/0DIF)
* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The projection-formula map after the tensored adjoint of `c : L K ⟶ M` is the unit at
`A (K, H)` followed by `R` of the comparison and `c`. -/
lemma map_adjunction_homEquiv_comp_adjunctionTensorMap {K : C} {M : D} (c : L.obj K ⟶ M)
    (H : C) :
    A.map (adj.homEquiv _ _ c ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α M H =
      adj.unit.app (A.obj (K, H)) ≫ R.map (α.app (K, H) ≫ B.map (c ×ₘ 𝟙 (L.obj H))) := by
  have h₁ : (adj.homEquiv _ _ c ×ₘ 𝟙 H : (K, H) ⟶ (R.obj M, H)) =
      (adj.unit.app K ×ₘ 𝟙 H) ≫ (R.map c ×ₘ 𝟙 H) := by
    rw [Adjunction.homEquiv_unit]
    exact Prod.ext rfl (Category.id_comp _).symm
  rw [h₁, A.map_comp, Category.assoc, adjunctionTensorMap_natural adj A B α c (𝟙 H),
    ← Category.assoc, adjunctionTensorMap_unit, Adjunction.homEquiv_unit, Category.assoc,
    ← R.map_comp, L.map_id]

end CategoryTheory

namespace StacksDraft.DerivedInverseLimit

/-- The base-change morphism adjoint to a morphism into a derived restriction of scalars is
natural in the target. -/
theorem derivedBaseChangeComparison_comp_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {X : DerivedCategory (ModuleCat.{u} R)}
    {Y Y' : DerivedCategory (ModuleCat.{u} S)}
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) (h : Y ⟶ Y') :
    derivedBaseChangeComparison.{u, u, u} f
        (g ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map h) =
      derivedBaseChangeComparison.{u, u, u} f g ≫ h := by
  dsimp only [derivedBaseChangeComparison]
  exact Adjunction.homEquiv_naturality_right_symm _ g h

/-- **Two out of three for base-change comparisons.** If the comparisons adjoint to `g` and to
`g ≫ res(h)` are isomorphisms, then so is `h`. -/
theorem isIso_of_isIso_derivedBaseChangeComparison_comp_map {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) {X : DerivedCategory (ModuleCat.{u} R)}
    {Y Y' : DerivedCategory (ModuleCat.{u} S)}
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) (h : Y ⟶ Y')
    [IsIso (derivedBaseChangeComparison.{u, u, u} f g)]
    (hgh : IsIso (derivedBaseChangeComparison.{u, u, u} f
      (g ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map h))) :
    IsIso h := by
  rw [derivedBaseChangeComparison_comp_map] at hgh
  exact IsIso.of_isIso_comp_left (derivedBaseChangeComparison.{u, u, u} f g) h

end StacksDraft.DerivedInverseLimit

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)

variable (S : DerivedExistenceSituation.{u})

/-- **The restriction map `cₙ : Liₙ^*K ⟶ Kₙ`**: the adjoint of the projection
`πₙ : K ⟶ R(iₙ)_* Kₙ` of [Stacks, Tag 0DIC]. -/
def restrictionMap (n : ℕ) : (derivedPullback (S.levelInclusion n)).obj S.limitObject ⟶ S.K n :=
  ((derivedAdjunction (S.levelInclusion n)).homEquiv _ _).symm (S.limitProjection n)

/-- The underlying topological space of the scheme `X` is compact. -/
instance : CompactSpace S.X.left := by
  have := S.proper
  exact QuasiCompact.compactSpace_of_compactSpace S.X.hom

/-- `cₙ` is an isomorphism as soon as `RΓ(Xₙ, cₙ ⊗^𝐋 Liₙ^*E)` is one for every perfect `E`. -/
theorem isIso_restrictionMap_of_forall (n : ℕ)
    (h : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso ((derivedGlobalSectionsOver (levelStructure S.system S.X n)).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (schemeAt S.system S.X n).sheaf).map (S.restrictionMap n)).app
              ((derivedPullback (S.levelInclusion n)).obj E)))) :
    IsIso (S.restrictionMap n) := by
  have := S.closedSchemeProjection n
  exact isIso_of_isIso_derivedGlobalSectionsOver_map_derivedTensor
    (schemeProjection S.system S.X n) (levelStructure S.system S.X n) S.limitObject
    S.isQuasicoherent_homology_limitObject (S.K n)
    (isQuasicoherentDerived_of_isPseudoCoherent _ (S.K n) (S.pseudoCoherent n))
    (S.restrictionMap n) h

/-- **`cₙ` is an isomorphism once both base-change maps are**: if for every perfect `E` the
base-change comparisons of `RΓ(X, K ⊗^𝐋 E) ⟶ RΓ(Xₙ, Liₙ^*(K ⊗^𝐋 E))` (flat base change) and of
`RΓ(X, K ⊗^𝐋 E) ⟶ RΓ(Xₙ, Kₙ ⊗^𝐋 Liₙ^*E)` (the map of [Stacks, Tag 0DID], built from `cₙ`) are
isomorphisms, then `cₙ` is: the second comparison is the first followed by
`RΓ(Xₙ, cₙ ⊗^𝐋 Liₙ^*E)` up to the isomorphism of [Stacks, Tag 079U]. -/
theorem isIso_restrictionMap_of_isIso_tensorPullbackMap (n : ℕ)
    (hbc : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
          (limit.π S.system (op n)).hom
          (LerayOver.pullbackSectionsMap (limit.π S.system (op n)).hom S.X.hom
            (levelStructure S.system S.X n) (schemeProjection S.system S.X n)
            pullback.condition (((LerayOver.tensor S.X.left).obj S.limitObject).obj E))))
    (h : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
          (limit.π S.system (op n)).hom
          (LerayOver.tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom
            (levelStructure S.system S.X n) (schemeProjection S.system S.X n)
            pullback.condition E S.limitObject (S.K n) (S.restrictionMap n)))) :
    IsIso (S.restrictionMap n) := by
  refine S.isIso_restrictionMap_of_forall n fun E hE => ?_
  have := hbc E hE
  have h₁ := StacksDraft.DerivedInverseLimit.isIso_of_isIso_derivedBaseChangeComparison_comp_map
    _ _ _ (h E hE)
  have hp : IsIso (LerayOver.pullbackTensorHom (schemeProjection S.system S.X n)
      (S.limitObject : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing S.X.left.toRingedSpace))) E) :=
    ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      (schemeProjection S.system S.X n).toLRSHom.toShHom).app _).isIso_hom
  have h₂ := Functor.map_isIso (LerayOver.sections (levelStructure S.system S.X n))
    (LerayOver.pullbackTensorHom (schemeProjection S.system S.X n) S.limitObject E)
  rw [Functor.map_comp] at h₁
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₂ h₁

/-- **`cₙ` is an isomorphism once the comparison of [Stacks, Tag 0DID] is**: flat base change
([Stacks, Tag 08IB] over an affine base) supplies the other comparison, `X` being flat, proper
and of finite presentation over `A` and `Xₙ = X ×_{Spec A} Spec Aₙ`. -/
theorem isIso_restrictionMap_of_isIso_tensorPullbackMap_of_flat (n : ℕ)
    (h : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
          (limit.π S.system (op n)).hom
          (LerayOver.tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom
            (levelStructure S.system S.X n) (schemeProjection S.system S.X n)
            pullback.condition E S.limitObject (S.K n) (S.restrictionMap n)))) :
    IsIso (S.restrictionMap n) := by
  have := S.proper
  have := S.flat
  refine S.isIso_restrictionMap_of_isIso_tensorPullbackMap n (fun E hE => ?_) h
  exact LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap
    (limit.π S.system (op n)).hom S.X.hom (levelStructure S.system S.X n)
    (schemeProjection S.system S.X n)
    (IsPullback.of_hasPullback S.X.hom (baseProjection S.system n))
    _ (Stacks.Duality.isQuasicoherent_homology_derivedTensor_anyModel S.X.left _ E
      S.isQuasicoherent_homology_limitObject (isQuasicoherent_homology_of_isPerfect E hE))

/-- **The restriction of `K` to `Xₙ` is `Kₙ`**: the canonical map `cₙ : Liₙ^*K ⟶ Kₙ`, adjoint to
the projection `K ⟶ R(iₙ)_* Kₙ` of [Stacks, Tag 0DIC], is an isomorphism. The comparison of
[Stacks, Tag 0DID] is invertible for every perfect `E`, and it is flat base change followed by
`RΓ(Xₙ, cₙ ⊗^𝐋 Liₙ^*E)`; perfect twists detect isomorphisms out of a derived pullback along the
closed immersion `Xₙ ⟶ X`
(`AlgebraicGeometry.isIso_of_isIso_derivedGlobalSectionsOver_map_derivedTensor`). -/
theorem isIso_restrictionMap (n : ℕ) : IsIso (S.restrictionMap n) :=
  S.isIso_restrictionMap_of_isIso_tensorPullbackMap_of_flat n fun E hE =>
    S.isIso_derivedBaseChangeComparison_cohomologyMap E hE n

/-- The restriction map `cₙ : Liₙ^*K ⟶ Kₙ` is an isomorphism. -/
instance (n : ℕ) : IsIso (S.restrictionMap n) := S.isIso_restrictionMap n

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
