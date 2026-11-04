module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSmul

/-!
# Two ingredients for reading a trivialization on meromorphic sections

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `L` be
an `𝒪_F`-module. This file proves two facts about local freeness and meromorphic sections.

* **A one-element cofan is a trivialization.** Over an index type with one element, the
  injection of a cofan whose colimit its point is, is an isomorphism; so the local freeness of
  rank one of Stacks 0409's rank clause, a one-element cofan whose colimit the module is, gives
  an isomorphism with the structure sheaf.
* **The sheafification map of the meromorphic sections is locally injective.** Two meromorphic
  sections over a chart with the same image in the sheaf `𝒦_F(L)` of Stacks 0EN5 agree on a
  covering of that chart.

## Main results

* `CategoryTheory.Limits.isIso_cofanInj_of_unique`: the injection of a cofan over an index type
  with exactly one element, whose colimit its point is, is an isomorphism.
* `AlgebraicGeometry.Space.isLocallyInjective_toSheafify_meromorphicSectionModuleUp`: the
  sheafification map of the presheaf `L ⊗_{𝒪_F} 𝒦_F` of meromorphic sections is locally
  injective.
* `AlgebraicGeometry.Space.equalizerSieve_toMeromorphicSectionSheaf_mem`: two meromorphic
  sections over a chart with the same image in `𝒦_F(L)` agree on a covering sieve of that
  chart.

## Implementation notes

`AlgebraicGeometry.Space.toMeromorphicSectionSheaf` is the sheafification map precomposed with
the universe lift, so the equalizer sieve is the one of the lifted sections.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- **A cofan over an index type with exactly one element whose colimit its point is has that
one injection for an isomorphism.** -/
theorem isIso_cofanInj_of_unique {C : Type*} [Category C] {I : Type*} [Unique I]
    {f : I → C} {X : C} (ι : ∀ i, f i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    IsIso (ι default) := by
  set e := hc.coconePointUniqueUpToIso (colimitCoconeOfUnique f).isColimit with he
  have h : ι default ≫ e.hom = 𝟙 (f default) := by
    simpa [he] using IsColimit.comp_coconePointUniqueUpToIso_hom hc
      (colimitCoconeOfUnique f).isColimit (Discrete.mk (default : I))
  rw [(Iso.comp_hom_eq_id e).mp h]
  exact ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The sheafification map of the meromorphic sections is locally injective.**  Two sections of
the presheaf `L ⊗_{𝒪_F} 𝒦_F` over a chart with the same image in the sheaf `𝒦_F(L)` of
Stacks 0EN5 agree on a covering of that chart. -/
theorem isLocallyInjective_toSheafify_meromorphicSectionModuleUp
    (M : Modules.{u, u} B S hS F hF) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F)
        (meromorphicSectionModuleUp B S hS F hF M)) :=
  ((SmallEtale.topology B S hS F).W_toSheafify _).isLocallyInjective

/-- **Two meromorphic sections over a chart with the same image in `𝒦_F(L)` agree on a covering
sieve of that chart.**  If two sections `t, t'` of `L ⊗_{𝒪_F} 𝒦_F` over a chart `V` have the
same image in the sheaf `𝒦_F(L)` of Stacks 0EN5, then the sieve of morphisms into `V` along which
their restrictions agree is a covering sieve. -/
theorem equalizerSieve_toMeromorphicSectionSheaf_mem
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (t t' : (meromorphicSectionModule B S hS F hF M).obj (op V))
    (h : toMeromorphicSectionSheaf B S hS F hF M V t =
      toMeromorphicSectionSheaf B S hS F hF M V t') :
    Presheaf.equalizerSieve
        (F := meromorphicSectionModuleUp B S hS F hF M) (ULift.up t) (ULift.up t') ∈
      SmallEtale.topology B S hS F V :=
  (isLocallyInjective_toSheafify_meromorphicSectionModuleUp B S hS F hF M).equalizerSieve_mem
    (ULift.up t) (ULift.up t') h

end AlgebraicGeometry.Space

end
