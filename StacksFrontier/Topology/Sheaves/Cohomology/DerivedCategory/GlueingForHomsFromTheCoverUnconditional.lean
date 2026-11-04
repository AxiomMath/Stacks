module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheSheafCondition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingOverACoveringCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomPresheafValueRestrictionSquare

/-!
# Glueing morphisms in the derived category over a covering collection

Let `(X, 𝒪_X)` be a ringed space and let `ℬ` be a collection of open subsets covering `X` such
that the intersection of two members of `ℬ` is the union of the members of `ℬ` contained in it,
and let `K`, `L` be objects of `D(𝒪_X)` with `Ext^i(K|_U, L|_U) = 0` for `i < 0` and `U ∈ ℬ`.
Then at every open `O` that is the union of the members of `ℬ` contained in it, a family of
morphisms `K|_W ⟶ L|_W` indexed by those members and compatible with restriction between them is
the restriction of exactly one morphism `K|_O ⟶ L|_O`.

## Main results

* `Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_isBasis`:
  the glueing of morphisms over a basis of the target of a morphism of ringed spaces.
* `Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered` and
  `Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered`: the glueing of morphisms over
  a collection of opens that covers `X` and whose pairwise intersections are unions of members,
  at every open that the collection covers.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnboundedHigherDirectImage (preimageRestrict
  derivedPreimageHomPresheafValueEquiv_map)
open Stacks.SheafOfModules (homSheafObject ringedSite)

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_moduleSheaves

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {B : Set (Opens Y.carrier)}
  (hB : Opens.IsBasis B) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

include hB in
/-- **The glueing of morphisms over a basis** ([Stacks, Tag 0D66] part (2)). Let `B` be a basis
of `Y` such that the negative `Ext` groups between the restrictions of `K` and `L` to the
preimages of the members of `B` vanish. Then for every open `V₀` of `Y`, a family of morphisms
between the restrictions of `K` and `L` to the preimages of the members of `B` contained in `V₀`,
compatible with restriction, is the restriction of exactly one morphism over the preimage of
`V₀`. -/
theorem exists_unique_restrictDerivedHom_on_isBasis
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i))
    (V₀ : Opens Y.carrier)
    (φ : ∀ V ∈ B, V ≤ V₀ → ((preimageRestrict f V).obj K ⟶ (preimageRestrict f V).obj L))
    (hφ : ∀ (V V' : Opens Y.carrier) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVV₀ : V ≤ V₀),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hle.hom) K L
          (φ V hV hVV₀) = φ V' hV' (hle.trans hVV₀)) :
    ∃! ψ : (preimageRestrict f V₀).obj K ⟶ (preimageRestrict f V₀).obj L,
      ∀ (V : Opens Y.carrier) (hV : V ∈ B) (hVV₀ : V ≤ V₀),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hVV₀.hom) K L ψ =
          φ V hV hVV₀ :=
  exists_unique_restrictDerivedHom_of_isBasis f hB K L hExt
    (fun _ _ hV s => derivedPreimageHomPresheafValueEquiv_map f K L hV s) V₀ φ hφ

end Stacks.Cohomology.UnboundedHigherDirectImage

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The glueing of morphisms over a covering collection.** Let `ℬ` be a collection of opens
covering `X` such that the intersection of two members is the union of the members contained in
it and the negative `Ext` groups between the restrictions of `K` and `L` to the members vanish.
Then at every open `O` that is the union of the members contained in it, a family of morphisms
between the restrictions of `K` and `L` to the members contained in `O`, compatible with
restriction, is the restriction of exactly one morphism over `O`. -/
theorem exists_unique_restrictDerivedHom_on_sSup_covered
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O})
    (φ : ∀ U ∈ ℬ, U ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L))
    (hφ : ∀ (U U' : Opens X.carrier) (hU : U ∈ ℬ) (hU' : U' ∈ ℬ) (hle : U' ≤ U) (hUO : U ≤ O),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) hle.hom K L (φ U hU hUO) =
        φ U' hU' (hle.trans hUO)) :
    ∃! ψ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L,
      ∀ (U : Opens X.carrier) (hU : U ∈ ℬ) (hUO : U ≤ O),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) hUO.hom K L ψ = φ U hU hUO :=
  exists_unique_restrictDerivedHom_of_sSup_covered K L ℬ hcover hinter hExt
    (fun _ f _ _ hV s => derivedPreimageHomPresheafValueEquiv_map f K L hV s) O hO φ hφ

/-- The glueing of morphisms of
`Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered`, with the compatibility
of the family stated for each member `W` contained in `O` and each member `W'` contained in
`W`. -/
theorem existsUnique_hom_restrict_of_sSup_covered
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O})
    (φ : ∀ W ∈ ℬ, W ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj L))
    (hφ : ∀ (W : Opens X.carrier) (hW : W ∈ ℬ) (hWO : W ≤ O) (W' : Opens X.carrier)
        (hW' : W' ∈ ℬ) (h : W' ≤ W),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) h.hom K L (φ W hW hWO) =
        φ W' hW' (h.trans hWO)) :
    ∃! ψ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L,
      ∀ (W : Opens X.carrier) (hW : W ∈ ℬ) (hWO : W ≤ O),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) hWO.hom K L ψ = φ W hW hWO :=
  existsUnique_hom_restrict_of_sSup_covered_of_valueEquivMap ℬ hcover hinter K L
    (fun {_Y} f {_V _V'} hV s => derivedPreimageHomPresheafValueEquiv_map f K L hV s) hExt O hO
    φ hφ

end Stacks.DerivedGlueing

end
