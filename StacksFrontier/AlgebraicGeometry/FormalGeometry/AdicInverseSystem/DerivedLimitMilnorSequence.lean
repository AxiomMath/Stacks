module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.AffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase

/-!
# The derived limit of an adic inverse system and its Milnor sequence

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `(F_n)` an adic inverse system
of quasi-coherent modules with limit `F = lim F_n`. Placed in degree zero, `F` is a derived
inverse limit of the system, and consequently the cohomology of `F` sits in the Milnor short
exact sequence `0 → R¹ lim H^(p-1)(X, F_n) → H^p(X, F) → lim H^p(X, F_n) → 0`.

Both statements rest on the affine vanishing of
`Stacks.Algebraization.AdicInverseSystem.isZero_cohomology_limitModule_of_affineOpen`: the terms
of the system are quasi-coherent, hence acyclic on the affine opens, and the transitions are
surjective on affine sections, so `R¹ lim` of the sections vanishes there. Those are exactly the
two hypotheses under which the ordinary limit computes the derived one, and derived sections
commute with derived limits.

## Main results

* `Stacks.Algebraization.AdicInverseSystem.isDerivedLimit_single_limitModule` — the ordinary
  inverse limit, in degree zero, is a derived inverse limit of the system.
* `Stacks.Algebraization.AdicInverseSystem.exists_shortExact_cohomology_limitModule` — the
  Milnor short exact sequence `0 → R¹ lim H^(p-1)(X, F_n) → H^p(X, F) → lim H^p(X, F_n) → 0`.

## Implementation notes

Cohomology is read over a base ring `A` mapping to `Γ(X, 𝒪_X)`, as the homology of the derived
sections functor `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` applied to a
module placed in degree zero, and `R¹ lim` of a countable tower is the cokernel of the difference
map `1 - shift` on the product of its terms.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

namespace Stacks.Algebraization

namespace AdicInverseSystem

variable (S : AdicInverseSystem.{u})

open Pretriangulated RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase (derivedSectionsOver)

attribute [local instance] HasDerivedCategory.standard

/-- The inverse limit of an adic inverse system **is** its derived inverse limit: placed in
degree zero, `F = lim F_n` sits in the defining distinguished triangle
`F ⟶ ∏ F_n ⟶ ∏ F_n ⟶ F[1]` of `R lim F_n`.

The terms are quasi-coherent, hence acyclic on the affine opens, and the transitions are
surjective on affine sections, so `R¹ lim` of the sections vanishes there; those are exactly
the two hypotheses under which the ordinary limit computes the derived one. -/
@[stacks 0EI8 "part (1)"]
public theorem isDerivedLimit_single_limitModule :
    ∃ h : HasProduct (fun n : ℕ =>
        (S.system ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)))
        _ _ _ _ _ _
        (S.system ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0) h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0).obj S.limitModule) :=
  Stacks.Cohomology.SpaceInverseLimits.isDerivedLimit_single_limit_of_isBasis
    S.X.toRingedSpace S.system S.X.affineOpens S.X.isBasis_affineOpens
    (fun V hV n q hq => by
      have : (S.system.obj ⟨n⟩).IsQuasicoherent := S.isQuasicoherent ⟨n⟩
      exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S.X
        (S.system.obj ⟨n⟩) V hV q hq)
    (fun V hV =>
      Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _
        (fun n => S.surjective_transition_app ⟨V, hV⟩ n))

/-- **The Milnor short exact sequence of an adic inverse system.** For every degree `p` the
cohomology of `F = lim F_n` sits in a short exact sequence

`0 ⟶ R¹ lim H^(p-1)(X, F_n) ⟶ H^p(X, F) ⟶ lim H^p(X, F_n) ⟶ 0`.

Cohomology is read over a base ring `A` mapping to `Γ(X, 𝒪_X)` by `ρ`, as the degree-`p`
cohomology of `RΓ(X, -)` applied to a module placed in degree zero; for `A = Γ(X, 𝒪_X)` and
`ρ` the identity this is sheaf cohomology with its module structure, the identification being
`Stacks.Cohomology.ModuleComparison.hfunctorIsoHomologyDerivedSectionsOver`. `R¹ lim` is the
cokernel of the difference map `1 - shift` on the product of the groups `H^(p-1)(X, F_n)`.

The sequence comes from the Milnor triangle of `RΓ(X, F)`: the ordinary limit is a derived
limit of the system by `isDerivedLimit_single_limitModule`, and derived sections commute with
derived limits. The inclusion descends the connecting morphism of that triangle and the
projection is characterized by its composites with the limit projections. -/
@[stacks 0EI8 "part (3)"]
public theorem exists_shortExact_cohomology_limitModule {A : Type u} [CommRing A]
    (ρ : A →+* (structureSheafRing S.X.toRingedSpace).obj.obj
      (op (⊤ : Opens S.X.toRingedSpace.carrier))) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) :=
      S.system ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0
    let L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) :=
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0).obj S.limitModule
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      K ⋙ derivedSectionsOver S.X.toRingedSpace ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (derivedSectionsOver S.X.toRingedSpace ρ).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver S.X.toRingedSpace ρ).obj L)⟦(1 : ℤ)⟧),
      let T := Triangle.mk a d b
      T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
        ∀ p : ℤ,
          let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) p
          let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1)
          let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
          let P : ModuleCat.{u} A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
            (i : cokernel δ ⟶ H.obj ((derivedSectionsOver S.X.toRingedSpace ρ).obj L))
            (q : H.obj ((derivedSectionsOver S.X.toRingedSpace ρ).obj L) ⟶
              limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ Y ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (p - 1) p ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                H.map a ≫ H.map (Pi.π Y n)) ∧
              (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨h, hlim⟩ := S.isDerivedLimit_single_limitModule
  have := h
  exact Stacks.Cohomology.DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver
    S.X.toRingedSpace ρ _ _ hlim

end AdicInverseSystem

end Stacks.Algebraization

end

end
