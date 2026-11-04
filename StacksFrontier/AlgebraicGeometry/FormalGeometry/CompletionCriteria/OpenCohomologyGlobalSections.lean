module

public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Algebraization.GlobalSectionsComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologySpelling

/-!
# The cohomology of a system on `U` is the local cohomology of its global sections

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`, and let `(ℱₙ)` be a coherent `I`-adic
system on `U`.  Write `Mₙ = H⁰(U, ℱₙ)`, the `A`-module of global sections — this is
`Stacks.Algebraization.globalSectionsSystem`.

The proof of [Stacks, Tag 0DXU] reduces the tag to a statement about the image of the transition
map `H¹(U, ℱₙ) ⟶ H¹(U, ℱ₁)` and then rewrites that image as the image of
`H²_𝔪(Mₙ) ⟶ H²_𝔪(M₁)`, where local duality applies.  This file performs that rewriting, for
every degree `p ≥ 1` at once and as an isomorphism of inverse systems, so that the *maps* come
along and not merely the objects.

Two identifications are composed.  `Stacks.Algebraization.tildeGlobalSectionsRestrictIso` says
that `(Mₙ~)|_U ≅ ℱₙ` naturally in `n` ([Stacks, Tag 0EIR]); and
`Stacks.Algebraization.openCohomologyLocalCohomologyNatIso` says that
`H^p(U, N~|_U) ≅ H^{p+1}_𝔞(N)` naturally in the `A`-module `N` ([Stacks, Tag 0BK0] (2)).

## Main results

* `Stacks.Algebraization.isFiniteLength_range_of_natIso` — the finite length of the image of a
  transition map of an inverse system of modules is invariant under a natural isomorphism of
  systems.
* `Stacks.Algebraization.proj_eq_systemMap` — the iterated transition
  `Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj` of an adic system is the
  functorial map `ℱₙ ⟶ ℱ₁`.
* `Stacks.Algebraization.globalSectionsRestrictedTildeSystemIso` —
  `H⁰(U, ℱₙ)~|_U ≅ ℱₙ` in the `Stacks.Algebraization.restrictedTildeFunctor` spelling.
* `Stacks.Algebraization.globalSectionsLocalCohomologyOpenCohomologyIso` — for `p ≥ 1`,
  `H^{p+1}_𝔞(H⁰(U, ℱₙ)) ≅ H^p(U, ℱₙ)`, as an isomorphism of inverse systems.
* `isFiniteLength_range_openCohomology_of_isFiniteLength_range_localCohomology`
  — the finite length of the image of `H^{p+1}_𝔞(Mₙ) ⟶ H^{p+1}_𝔞(M₁)` gives the finite length of
  the image of `H^p(U, ℱₙ) ⟶ H^p(U, ℱ₁)`, which at `p = 1` is the input that
  `Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_isFiniteLength_range` consumes.

## Implementation notes

`Stacks.Algebraization.tildeGlobalSectionsRestrictIso` is stated with
`AlgebraicGeometry.Scheme.Modules.pullback` where
`Stacks.Algebraization.restrictedTildeFunctor` uses
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`; the two are identified by Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

The transition maps of the Mittag-Leffler criteria are written with
`Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj`, an iterated composite defined by
recursion, while a natural isomorphism of systems transports the *functorial* map
`F.obj.map (homOfLE _).op`.  `Stacks.Algebraization.proj_eq_systemMap` identifies the two; the
hom sets of `ℕ` are subsingletons, so the only content is the recursion.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0DXG](https://stacks.math.columbia.edu/tag/0DXG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Transporting the image of a transition map along a natural isomorphism -/

/-- **The image of a transition map, up to a natural isomorphism of systems.**  Let `G` and `G'`
be functors into `A`-modules and let `e : G ≅ G'`.  If the image of `G.map φ` has finite length,
so has the image of `G'.map φ`.

The naturality square writes `G'.map φ` as `e.inv ≫ G.map φ ≫ e.hom`; the first factor is
surjective, so the image of `G'.map φ` is the image of the image of `G.map φ` under the
injective map `e.hom`. -/
theorem isFiniteLength_range_of_natIso {A : Type u} [CommRing A] {J : Type*} [Category J]
    {G G' : J ⥤ ModuleCat.{u} A} (e : G ≅ G') {X Y : J} (φ : X ⟶ Y)
    (h : IsFiniteLength A (LinearMap.range (G.map φ).hom)) :
    IsFiniteLength A (LinearMap.range (G'.map φ).hom) := by
  have hnat : G.map φ ≫ e.hom.app Y = e.hom.app X ≫ G'.map φ := e.hom.naturality φ
  have hG' : G'.map φ = e.inv.app X ≫ G.map φ ≫ e.hom.app Y := by
    rw [hnat, ← Category.assoc, ← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  have hsurj : Function.Surjective (e.inv.app X).hom :=
    ((e.app X).symm.toLinearEquiv).surjective
  have hinj : Function.Injective (e.hom.app Y).hom := ((e.app Y).toLinearEquiv).injective
  have hrange : LinearMap.range (G'.map φ).hom =
      Submodule.map (e.hom.app Y).hom (LinearMap.range (G.map φ).hom) := by
    rw [hG', ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj),
      LinearMap.range_comp]
  rw [hrange]
  exact (Submodule.equivMapOfInjective (e.hom.app Y).hom hinj _).isFiniteLength h

/-! ### The iterated transition map of an adic system -/

/-- The iterated transition map `ℱₙ ⟶ ℱ₁` of a coherent adic system, as the recursion
`Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj` builds it, is the functorial map
along `0 ≤ n` in `ℕᵒᵖ`. -/
theorem proj_eq_systemMap (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (n : ℕ) :
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
        (systemObj S F) (systemMapSucc S F) n =
      F.obj.map (homOfLE (Nat.zero_le n)).op := by
  induction n with
  | zero => exact (F.obj.map_id _).symm
  | succ n ih =>
    have hstep : Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
        (systemObj S F) (systemMapSucc S F) (n + 1) =
          systemMapSucc S F n ≫ Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
            (systemObj S F) (systemMapSucc S F) n := rfl
    rw [hstep, ih, ← F.obj.map_comp]
    rfl

/-! ### The two identifications -/

/-- **[Stacks, Tag 0EIR] in the `restrictedTildeFunctor` spelling.**  The restriction to `U` of
the sheaf on `X = Spec(A)` attached to the `A`-module `H⁰(U, ℱₙ)` is `ℱₙ`, naturally in `n`. -/
def globalSectionsRestrictedTildeSystemIso (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    globalSectionsSystem S F ⋙ restrictedTildeFunctor S ≅ F.obj :=
  Functor.isoWhiskerLeft (globalSectionsSystem S F ⋙ tilde.functor (.of S.A))
      (Scheme.Modules.restrictFunctorIsoPullback S.U.ι) ≪≫
    tildeGlobalSectionsRestrictIso S F

/-- **The cohomology of the system on `U` is the local cohomology of its global sections.**  For
`p ≥ 1` the inverse system `H^{p+1}_𝔞(H⁰(U, ℱₙ))` is isomorphic to the inverse system
`H^p(U, ℱₙ)`, the isomorphism being natural in `n` and so carrying the transition maps along.

This is [Stacks, Tag 0EIR] followed by [Stacks, Tag 0BK0] (2).  It is the step with which the
proof of [Stacks, Tag 0DXU] turns its claim about the image of `H¹(U, ℱₙ) ⟶ H¹(U, ℱ₁)` into a
claim about the image of `H²_𝔪(Mₙ) ⟶ H²_𝔪(M₁)`. -/
def globalSectionsLocalCohomologyOpenCohomologyIso (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (p : ℕ) (hp : 0 < p) :
    globalSectionsSystem S F ⋙
        localCohomologyDegreeFunctor S.A S.a (Ideal.fg_of_isNoetherianRing S.a) ((p : ℤ) + 1) ≅
      F.obj ⋙ openCohomologyFunctor S p :=
  (Functor.isoWhiskerLeft (globalSectionsSystem S F)
      (openCohomologyLocalCohomologyNatIso S p hp)).symm ≪≫
    Functor.isoWhiskerRight (globalSectionsRestrictedTildeSystemIso S F)
      (openCohomologyFunctor S p)

/-! ### The finite-length statement 0DXU consumes -/

/-- **The reduction of condition (a) of [Stacks, Tag 0EHH] to local cohomology.**  Let `(ℱₙ)` be
a coherent `I`-adic system on `U = X ∖ V(𝔞)`, let `p ≥ 1`, and write `Mₙ = H⁰(U, ℱₙ)`.  If the
image of

  `H^{p+1}_𝔞(Mₙ) ⟶ H^{p+1}_𝔞(M₁)`

has finite length as an `A`-module, then so has the image of `H^p(U, ℱₙ) ⟶ H^p(U, ℱ₁)`.

At `p = 1` the conclusion is exactly the hypothesis `harange` of
`Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_isFiniteLength_range`, i.e. the
last step of the proof of [Stacks, Tag 0DXU] in the spelling [Stacks, Tag 0DXG] consumes; and
the hypothesis is the statement to which that proof applies local duality and Matlis duality. -/
theorem isFiniteLength_range_openCohomology_of_isFiniteLength_range_localCohomology
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (p : ℕ) (hp : 0 < p) (n : ℕ)
    (h : IsFiniteLength S.A (LinearMap.range
      ((localCohomologyDegreeFunctor S.A S.a (Ideal.fg_of_isNoetherianRing S.a)
            ((p : ℤ) + 1)).map
        ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom)) :
    IsFiniteLength S.A (LinearMap.range
      ((openCohomologyFunctor S p).map
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
          (systemObj S F) (systemMapSucc S F) n)).hom) := by
  rw [proj_eq_systemMap S F n]
  exact isFiniteLength_range_of_natIso
    (globalSectionsLocalCohomologyOpenCohomologyIso S F p hp)
    (homOfLE (Nat.zero_le n)).op h

end Stacks.Algebraization

end
