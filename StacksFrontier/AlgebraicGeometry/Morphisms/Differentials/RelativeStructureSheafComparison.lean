module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialOperators
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.CommRingToRingPullback

/-!
# The two inverse images of the structure sheaf of the target of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f⁻¹𝒪_Y` of the structure sheaf of
`Y` can be formed either in sheaves of commutative rings, which is the structure sheaf of the
inverse-image ringed space `(X, f⁻¹𝒪_Y)`, or in sheaves of rings after forgetting
commutativity, which is the source of `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap`
and so the ring relative to which differential operators on `X/Y` are defined. The two
sheafifications are canonically isomorphic, compatibly with their maps to `𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.toCommRingCatSheafHom` and
  `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMapCommRingCat` are the sheaf-of-commutative
  rings analogues of `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` and
  `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap`.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingSheafComparison` is the isomorphism between the
  two inverse images of `𝒪_Y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingSheafComparison_hom_comp` is the compatibility of
  the isomorphism with the two relative structure sheaf maps: it carries
  `relativeStructureSheafMapCommRingCat` to `relativeStructureSheafMap`.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingSheafComparison_codomain` identifies the
  codomain of the isomorphism with the sheaf of rings of the inverse-image ringed space.

## Implementation notes

Both statements are instances of the general comparison
`CategoryTheory.Functor.sheafPullbackSheafComposeIso` for the continuous functor
`TopologicalSpace.Opens.map f.base` and the forgetful functor `CommRingCat ⥤ RingCat`; the
latter preserves filtered colimits and sheafification, and the comma categories computing the
presheaf-level left Kan extension along `(Opens.map f.base).op` are filtered.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
  RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The morphism of sheaves of commutative rings `𝒪_Y ⟶ f_*𝒪_X` attached to a morphism of
schemes. -/
def toCommRingCatSheafHom :
    Y.sheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u} _ _).obj X.sheaf where
  hom := f.c

/-- The structural morphism `f⁻¹𝒪_Y ⟶ 𝒪_X` from the inverse image of the structure sheaf of the
target, formed in sheaves of commutative rings. -/
noncomputable def relativeStructureSheafMapCommRingCat :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
    f.toCommRingCatSheafHom

/-- The comparison between the inverse image of `𝒪_Y` formed in sheaves of rings and the inverse
image formed in sheaves of commutative rings. -/
noncomputable def inverseImageRingSheafComparison :
    (TopCat.Sheaf.pullback RingCat.{u} f.base).obj Y.ringCatSheaf ≅
      (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) :=
  TopCat.Sheaf.pullbackForget₂Iso f.base Y.sheaf

/-- The forward map of `inverseImageRingSheafComparison f` is the general comparison
`CategoryTheory.Functor.sheafPullbackSheafComposeHom` for `Opens.map f.base` and the forgetful
functor `CommRingCat ⥤ RingCat`. -/
lemma inverseImageRingSheafComparison_hom :
    (inverseImageRingSheafComparison f).hom =
      Functor.sheafPullbackSheafComposeHom (Opens.map f.base) CommRingCat.{u}
        (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
        (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u}) Y.sheaf :=
  rfl

/-- The codomain of the comparison is the sheaf of rings underlying the structure sheaf of the
inverse-image ringed space `(X, f⁻¹𝒪_Y)`. -/
theorem inverseImageRingSheafComparison_codomain :
    (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) =
      structureSheafRing (RingedSpace.inverseImage Y.toRingedSpace f.base) :=
  rfl

/-- The image of `toCommRingCatSheafHom f` under the forgetful functor to sheaves of rings,
composed with the identification of pushforwards, is `toRingCatSheafHom f`. -/
theorem sheafCompose_map_toCommRingCatSheafHom :
    (sheafCompose (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u})).map f.toCommRingCatSheafHom ≫
        (Functor.sheafComposeSheafPushforwardIso (Opens.map f.base) CommRingCat.{u}
          (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
          (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u})).inv.app X.sheaf =
      f.toRingCatSheafHom := by
  simp only [Functor.sheafComposeSheafPushforwardIso, Iso.refl_inv]
  rfl

/-- The comparison carries the relative structure sheaf map formed in sheaves of commutative
rings to the relative structure sheaf map formed in sheaves of rings. -/
theorem inverseImageRingSheafComparison_hom_comp :
    (inverseImageRingSheafComparison f).hom ≫
        (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            f.relativeStructureSheafMapCommRingCat =
      f.relativeStructureSheafMap := by
  have h1 : (inverseImageRingSheafComparison f).hom ≫
      (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u})).map f.relativeStructureSheafMapCommRingCat =
      Functor.sheafPullbackSheafComposeHom (Opens.map f.base) CommRingCat.{u}
          (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
          (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u}) Y.sheaf ≫
        (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((((Opens.map f.base).sheafAdjunctionContinuous CommRingCat.{u}
              (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
              (Opens.grothendieckTopology (X.carrier : TopCat.{u}))).homEquiv
            Y.sheaf X.sheaf).symm f.toCommRingCatSheafHom) := rfl
  have h3 : (((Opens.map f.base).sheafAdjunctionContinuous RingCat.{u}
        (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
        (Opens.grothendieckTopology (X.carrier : TopCat.{u}))).homEquiv
        ((sheafCompose (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.sheaf)
        ((sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).symm
        f.toRingCatSheafHom = f.relativeStructureSheafMap := rfl
  exact h1.trans
    (((Functor.sheafPullbackSheafComposeHom_comp_sheafCompose_map (Opens.map f.base)
        CommRingCat.{u} (Opens.grothendieckTopology (Y.carrier : TopCat.{u}))
        (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u}) Y.sheaf X.sheaf
        f.toCommRingCatSheafHom).trans
      (congrArg _ (sheafCompose_map_toCommRingCatSheafHom f))).trans h3)

end Scheme.Hom

end AlgebraicGeometry
