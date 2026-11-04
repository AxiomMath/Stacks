module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf

/-!
# Zariski glueing of a morphism of sheaves of modules, in the pullback spelling

Let `M` and `N` be sheaves of modules on a scheme `X`.  A morphism `M ⟶ N` may be restricted to
an open `W` of `X` in two ways: as
`AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι`, which is a restriction of sections, or
as `AlgebraicGeometry.Scheme.Modules.pullback W.ι`, which is the left adjoint of pushforward
built by general nonsense.  The two agree, by Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and glueing of a morphism out of
local data is available in the `restrictFunctor` spelling as
`Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_restrictHomLE`.  This
file transports that glueing to the `pullback` spelling.

The transport is not naturality: the local data is restricted to a smaller open by
`Stacks.AlgebraicGeometry.ModuleLimits.canStep` on the `pullback` side and by
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLE` on the `restrictFunctor` side, and
identifying the two is the compatibility of the comparison with the composition isomorphisms
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` — that is, the statement that the comparison of
the two left adjoints of pushforward along an open immersion is a *morphism of pseudofunctors*.
Its object half is `Stacks.Sites.restrictFunctorIsoPullback_comp`; this file records the half
that acts on morphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictHomEquivPullbackHom`: the bijection, induced by the
  comparison, between the morphisms of the restrictions of `M` and `N` along an open immersion
  and the morphisms of their pullbacks.

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_comp_of_eq`: **the comparison is
  compatible with composition**, for a composite of open immersions presented as a named
  morphism together with its equation.  This is
  `Stacks.Sites.restrictFunctorIsoPullback_comp` with the congruence isomorphisms folded in.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_app_comp_canStep`:
  **the morphism half of the morphism-of-pseudofunctors statement.**  Carrying a morphism of
  pullbacks one open immersion further, which is `canStep`, corresponds under the comparison to
  restricting the corresponding morphism of restrictions one open immersion further.  This is a
  candidate for Mathlib: it is mate calculus for the two left adjoints of pushforward along an
  open immersion, and nothing about schemes beyond that enters.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLEComp_restrictHomEquivPullbackHom_symm`: the
  same for two opens `Z ≤ W` of `X`, where the left-hand side is literally
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLEComp`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_cover`: **Zariski glueing of a
  morphism of sheaves of modules, in the pullback spelling.**  The overlap of two members of the
  covering may be enlarged to any open contained in both members and containing it, exactly as
  in `exists_restrictFunctor_map_eq_of_restrictHomLE`, which is what lets a consumer use the
  open its own argument produced rather than the intersection.

## Implementation notes

Both compatibility statements are stated for a composite `l ≫ j = k` of open immersions of
schemes presented as a *named* morphism `k` with its equation, rather than for the composite
`l ≫ j` itself.  This is what the consumers need — the composite in play is
`X.homOfLE h ≫ W.ι = Z.ι` — and it is also what avoids `subst`, since the congruence
isomorphisms are then eliminated by `Stacks.Sites.restrictFunctorIsoPullback_congr` rather than
by substituting `k`.

The uniqueness half of the glueing in this spelling is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover`, which needs the comparison
only through its naturality and is therefore independent of everything here.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Comparison

variable {X Y Y' : Scheme.{u}}

/-- **Restriction along an open immersion is pullback, compatibly with composition**, for a
composite presented as a named morphism `k` together with an equation `l ≫ j = k`.

This is `Stacks.Sites.restrictFunctorIsoPullback_comp` with the congruence isomorphisms of
`restrictFunctor` and of `pullback` folded in, and it is the object half of the statement that
`restrictFunctorIsoPullback` is a morphism of pseudofunctors. -/
theorem restrictFunctorIsoPullback_comp_of_eq (l : Y' ⟶ Y) (j : Y ⟶ X) (k : Y' ⟶ X)
    (hk : l ≫ j = k) [IsOpenImmersion l] [IsOpenImmersion j] [IsOpenImmersion k]
    (M : X.Modules) :
    (restrictFunctorCongr hk).inv.app M ≫ (restrictFunctorComp l j).hom.app M ≫
        (restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M) ≫
        (restrictFunctorIsoPullback l).hom.app ((pullback j).obj M) ≫
        (pullbackComp l j).hom.app M ≫ (pullbackCongr hk).hom.app M =
      (restrictFunctorIsoPullback k).hom.app M := by
  have hc := NatTrans.congr_app (Stacks.Sites.restrictFunctorIsoPullback_congr hk) M
  simp only [NatTrans.comp_app] at hc
  rw [reassoc_of% (Stacks.Sites.restrictFunctorIsoPullback_comp l j M), ← hc,
    Iso.inv_hom_id_app_assoc]

/-- The comparison `restrictFunctorIsoPullback` identifies the morphisms of the restrictions of
`M` and `N` along an open immersion `f` with the morphisms of their pullbacks along `f`. -/
noncomputable def restrictHomEquivPullbackHom (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    ((restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) ≃
      ((pullback f).obj M ⟶ (pullback f).obj N) :=
  ((restrictFunctorIsoPullback f).app M).homCongr ((restrictFunctorIsoPullback f).app N)

/-- `restrictHomEquivPullbackHom` is conjugation by the comparison. -/
theorem restrictHomEquivPullbackHom_apply (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules)
    (χ : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    restrictHomEquivPullbackHom f M N χ =
      (restrictFunctorIsoPullback f).inv.app M ≫ χ ≫
        (restrictFunctorIsoPullback f).hom.app N :=
  rfl

/-- `restrictHomEquivPullbackHom` is conjugation by the comparison, in the other direction. -/
theorem restrictHomEquivPullbackHom_symm_apply (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules)
    (θ : (pullback f).obj M ⟶ (pullback f).obj N) :
    (restrictHomEquivPullbackHom f M N).symm θ =
      (restrictFunctorIsoPullback f).hom.app M ≫ θ ≫
        (restrictFunctorIsoPullback f).inv.app N :=
  rfl

/-- The bijection `restrictHomEquivPullbackHom` carries the restriction of a morphism `M ⟶ N` to
its pullback: on morphisms coming from `X` it is the naturality of the comparison. -/
theorem restrictHomEquivPullbackHom_restrictFunctor_map (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) (φ : M ⟶ N) :
    restrictHomEquivPullbackHom f M N ((restrictFunctor f).map φ) = (pullback f).map φ := by
  rw [restrictHomEquivPullbackHom_apply, (restrictFunctorIsoPullback f).hom.naturality φ,
    Iso.inv_hom_id_app_assoc]

end Comparison

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.ModuleLimits

section Step

variable {X Y Y' : Scheme.{u}} (M N : X.Modules)

/-- **The comparison of restriction with pullback along an open immersion is a morphism of
pseudofunctors, read on morphisms.**  Carrying a morphism of the pullbacks of `M` and `N` along
`j` one open immersion `l` further, which is
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`, corresponds under
`AlgebraicGeometry.Scheme.Modules.restrictHomEquivPullbackHom` to restricting the corresponding
morphism of restrictions along `l`, conjugated by the composition and congruence isomorphisms of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

This is mate calculus for the two left adjoints of
`AlgebraicGeometry.Scheme.Modules.pushforward` along an open immersion, and is a candidate for
Mathlib: nothing beyond
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_comp_of_eq` and the naturality of
the comparison enters. -/
theorem restrictFunctorIsoPullback_hom_app_comp_canStep (l : Y' ⟶ Y) (j : Y ⟶ X) (k : Y' ⟶ X)
    (hk : l ≫ j = k) [IsOpenImmersion l] [IsOpenImmersion j] [IsOpenImmersion k]
    (θ : (Scheme.Modules.pullback j).obj M ⟶ (Scheme.Modules.pullback j).obj N) :
    (restrictFunctorIsoPullback k).hom.app M ≫ canStep l j k hk θ =
      ((restrictFunctorCongr hk).inv.app M ≫ (restrictFunctorComp l j).hom.app M ≫
          (restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M ≫ θ ≫
            (restrictFunctorIsoPullback j).inv.app N) ≫
          (restrictFunctorComp l j).inv.app N ≫ (restrictFunctorCongr hk).hom.app N) ≫
        (restrictFunctorIsoPullback k).hom.app N := by
  have hcs := canHom_comp_canStep l j k hk θ
  rw [canHom, canHom] at hcs
  simp only [Category.assoc] at hcs
  rw [← restrictFunctorIsoPullback_comp_of_eq l j k hk M,
    ← restrictFunctorIsoPullback_comp_of_eq l j k hk N]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rw [Functor.map_comp, Category.assoc,
    reassoc_of% ((restrictFunctorIsoPullback l).hom.naturality θ), hcs]

/-- `restrictFunctorIsoPullback_hom_app_comp_canStep` for two opens `Z ≤ W` of `X`, where the
left-hand side is by definition
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLEComp`.  This is the form the glueing uses:
it says that the agreement of local morphisms of pullbacks over the overlaps, stated with
`canStep`, is exactly the agreement in the `restrictFunctor` spelling that
`exists_restrictFunctor_map_eq_of_restrictHomLEComp` asks for. -/
theorem restrictHomLEComp_restrictHomEquivPullbackHom_symm {W Z : X.Opens} (h : Z ≤ W)
    (θ : (Scheme.Modules.pullback W.ι).obj M ⟶ (Scheme.Modules.pullback W.ι).obj N) :
    restrictHomLEComp h ((restrictHomEquivPullbackHom W.ι M N).symm θ) =
      (restrictHomEquivPullbackHom Z.ι M N).symm
        (canStep (X.homOfLE h) W.ι Z.ι (X.homOfLE_ι h) θ) := by
  rw [restrictHomLEComp]
  simp only [restrictHomEquivPullbackHom_symm_apply]
  rw [reassoc_of% (restrictFunctorIsoPullback_hom_app_comp_canStep M N (X.homOfLE h) W.ι Z.ι
      (X.homOfLE_ι h) θ), Iso.hom_inv_id_app, Category.comp_id]

end Step

section Glue

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **Zariski glueing of a morphism of sheaves of modules, in the pullback spelling.**  Given a
family of opens covering a scheme `X`, a morphism of the pullbacks of `M` and `N` along the
inclusion of each member, and the agreement of any two of them over an open containing the
overlap of the two members, there is a morphism `M ⟶ N` pulling back to each of them.

As in `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_restrictHomLE` the
overlap may be enlarged to any open contained in both members and containing it, which is what
lets a consumer use the open its own argument produced.

The morphism so obtained is unique, by
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover`. -/
theorem exists_pullback_map_eq_of_cover {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ a, x ∈ U a)
    (Z : ι → ι → X.Opens) (hZ₁ : ∀ a b, Z a b ≤ U a) (hZ₂ : ∀ a b, Z a b ≤ U b)
    (hZ : ∀ a b, U a ⊓ U b ≤ Z a b)
    (η : ∀ a, (Scheme.Modules.pullback (U a).ι).obj M ⟶
      (Scheme.Modules.pullback (U a).ι).obj N)
    (hagree : ∀ a b,
      canStep (X.homOfLE (hZ₁ a b)) (U a).ι (Z a b).ι (X.homOfLE_ι (hZ₁ a b)) (η a)
        = canStep (X.homOfLE (hZ₂ a b)) (U b).ι (Z a b).ι (X.homOfLE_ι (hZ₂ a b)) (η b)) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.pullback (U a).ι).map φ = η a := by
  obtain ⟨φ, hφ⟩ := exists_restrictFunctor_map_eq_of_restrictHomLEComp U hU
    (fun a => (restrictHomEquivPullbackHom (U a).ι M N).symm (η a)) Z hZ₁ hZ₂ hZ fun a b => by
      rw [restrictHomLEComp_restrictHomEquivPullbackHom_symm,
        restrictHomLEComp_restrictHomEquivPullbackHom_symm, hagree a b]
  refine ⟨φ, fun a => ?_⟩
  rw [← restrictHomEquivPullbackHom_restrictFunctor_map (U a).ι M N φ, hφ a,
    Equiv.apply_symm_apply]

end Glue

end Stacks.AlgebraicGeometry.ModuleLimits

end
