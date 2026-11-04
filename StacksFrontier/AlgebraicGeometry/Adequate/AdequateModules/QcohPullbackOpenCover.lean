module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.UniversalQuasiIso
public import StacksFrontier.AlgebraicGeometry.Modules.OpenCoverAcyclic

/-!
# Universal acyclicity is tested on affine targets

`Stacks.Adequate.universallyAcyclic` and `Stacks.Adequate.universalQuasiIso` quantify over
**every** morphism of schemes `T ⟶ S`. The last step of [Stacks, Tag 06ZR] needs them tested
only over the affine `T`, the source passing from an affine to a general base by an open cover.
This module supplies that passage, and the composition isomorphism for
`Stacks.Adequate.qcohPullback` on which it rests.

## Main definitions

* `Stacks.Adequate.qcohPullbackComp` — the composition isomorphism
  `qcohPullback (g ≫ f) ≅ qcohPullback f ⋙ Scheme.Modules.pullback g`. Pullback of
  quasi-coherent modules is contravariant and lands in *all* modules on the target, so the outer
  factor is the pullback of all modules, not a second `qcohPullback`.

## Main results

* `Stacks.Adequate.universallyAcyclic_of_affine` — **a complex whose pullback to every affine
  scheme over `S` is acyclic is universally acyclic.**
* `Stacks.Adequate.universalQuasiIso_of_affine` — the same for the universal
  quasi-isomorphisms.

## Implementation notes

The composition isomorphism is Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackComp`
whiskered with the inclusion of the quasi-coherent modules; the associativity coherence is
definitional, so `CategoryTheory.Functor.associator` has identity components here and no
`eqToHom` bookkeeping arises.

The reduction itself is: cover `T` by its affine opens, which is
`AlgebraicGeometry.iSup_affineOpens_eq_top`; the pullback along the inclusion of an affine open
`U ⊆ T` of the pullback along `f` is the pullback along `U.ι ≫ f`, whose source is affine; and
acyclicity in `K⁺(Mod(𝒪_T))` is local on an open cover, which is
`Stacks.AlgebraicGeometry.Modules.plus_subcategoryAcyclic_of_pullback`. The passage between the
two readings of the iterated pullback is the composition isomorphism above, carried into the
bounded below homotopy category by `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`.

Both statements are given over the preadditive and additive structures that instance search
finds, as `Stacks.Adequate.universallyAcyclic_iff` and `Stacks.Adequate.universalQuasiIso_eq_trW`
are: the triangulated structure of `K⁺(QCoh(𝒪_S))` is built from the preadditive structure a
full subcategory inherits from its ambient category, so an assumed `Preadditive` hypothesis
would leave it unsynthesizable.

Affineness of the target is an explicit hypothesis `IsAffine T` rather than an instance
argument, so that a consumer can discharge it with the `IsAffineOpen` witness of a member of the
affine cover, which is that statement on the nose.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Adequate

variable {S : Scheme.{u}}

/-! ### The composition isomorphism -/

/-- **Pullback of quasi-coherent modules along a composition.** For `g : T' ⟶ T` and
`f : T ⟶ S`, pulling a quasi-coherent `𝒪_S`-module back along `g ≫ f` is pulling it back along
`f` and then pulling the resulting `𝒪_T`-module back along `g`. This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackComp` whiskered with the inclusion of the
quasi-coherent modules. -/
public noncomputable def qcohPullbackComp {T T' : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ S) :
    qcohPullback (g ≫ f) ≅ qcohPullback f ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.pullbackComp g f).symm ≪≫
    (Functor.associator _ _ _).symm

/-! ### Testing universal acyclicity on the affines -/

/-- **A bounded below complex of quasi-coherent `𝒪_S`-modules whose pullback to every affine
scheme over `S` is acyclic is universally acyclic.** Given `f : T ⟶ S` with `T` arbitrary, cover
`T` by its affine opens; the pullback along the inclusion of an affine open `U` of the pullback
along `f` is the pullback along `U.ι ≫ f`, which the hypothesis makes acyclic, and acyclicity in
`K⁺(Mod(𝒪_T))` is local on an open cover. -/
public theorem universallyAcyclic_of_affine
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ S), IsAffine T →
      HomotopyCategory.Plus.subcategoryAcyclic T.Modules
        ((qcohPullback f).mapHomotopyCategoryPlus.obj K)) :
    universallyAcyclic S K := by
  rw [universallyAcyclic_iff]
  intro T f
  refine AlgebraicGeometry.Modules.plus_subcategoryAcyclic_of_pullback
    (fun U : T.affineOpens => U.1) (iSup_affineOpens_eq_top T) _ fun U => ?_
  exact (HomotopyCategory.Plus.subcategoryAcyclic _).prop_of_iso
    ((Functor.mapHomotopyCategoryPlusCompIso
      (qcohPullbackComp (U.1).ι f).symm).app K).symm (h _ ((U.1).ι ≫ f) U.2)

/-- **A morphism of `K⁺(QCoh(𝒪_S))` whose pullback to every affine scheme over `S` is a
quasi-isomorphism is a universal quasi-isomorphism.** The universal quasi-isomorphisms are the
morphisms whose cone is universally acyclic, by
`Stacks.Adequate.universalQuasiIso_eq_trW`, and likewise degreewise for the quasi-isomorphisms
of `K⁺(Mod(𝒪_T))`; so this is
`Stacks.Adequate.universallyAcyclic_of_affine` applied to that cone. -/
public theorem universalQuasiIso_of_affine
    {K L : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : K ⟶ L)
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ S), IsAffine T →
      HomotopyCategory.Plus.quasiIso T.Modules
        ((qcohPullback f).mapHomotopyCategoryPlus.map φ)) :
    universalQuasiIso S φ := by
  obtain ⟨Z, g, c, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  rw [universalQuasiIso_eq_trW]
  refine ((universallyAcyclic S).trW_iff_of_distinguished _ hT).2
    (universallyAcyclic_of_affine Z fun T f hTaff => ?_)
  have hq := h T f hTaff
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW] at hq
  exact ((HomotopyCategory.Plus.subcategoryAcyclic T.Modules).trW_iff_of_distinguished _
    ((qcohPullback f).mapHomotopyCategoryPlus.map_distinguished _ hT)).1 hq

end Stacks.Adequate

end
