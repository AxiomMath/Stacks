module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposCotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` the cotangent complex `L_{X/Y}` is the cotangent complex
of `f` read as a morphism of ringed topoi between the small Zariski sites, that is the cotangent
complex `L_{𝒪_X/f⁻¹𝒪_Y}` of the inverse-image form of `f♯` on the site of opens of `X`. The
inverse-image functor `𝒪 ↦ f⁻¹𝒪` of open sets preserves finite intersections and the whole
space, so it is representably flat and the induced continuous functor of sites is a morphism of
sites, which is what produces the morphism of topoi.

## Main definitions

* `TopologicalSpace.Opens.isMorphismOfSites_map`: taking inverse images of open sets along a
  continuous map is a morphism of the sites of opens.
* `AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom` is `f` read as a morphism of the Zariski
  ringed topoi of `X` and `Y`.
* `AlgebraicGeometry.Scheme.Hom.cotangentComplex` is `L_{X/Y}`, and
  `AlgebraicGeometry.Scheme.Hom.cotangentComplexDerived` is its image in the derived category of
  sheaves of `𝒪_X`-modules.

## Main results

* `TopologicalSpace.Opens.representablyFlat_map`: the inverse image of open sets along a
  continuous map is representably flat.
* `AlgebraicGeometry.Scheme.Hom.cotangentComplex_isZero_pos`: `L_{X/Y}` vanishes in positive
  cohomological degrees.

## Implementation notes

The structure map of the morphism of ringed topoi is `f.c` itself: the direct image of sheaves
of sets along the morphism of topoi induced by a morphism of sites is restriction along the
inverse-image functor of opens, and transporting the ring operations through that restriction
gives back the restriction of the sheaf of rings on the nose
(`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`), so no comparison of sections
intervenes.

The sites of opens of a scheme of universe `u` have both their objects and their morphisms in
`Type u`, and `𝒪_X` takes values in `CommRingCat.{u}`, which is the universe range of the
cotangent complex of a morphism of ringed topoi.

## References

* [Stacks Project, Tag 08T2](https://stacks.math.columbia.edu/tag/08T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback

universe u

namespace TopologicalSpace.Opens

/-- Taking inverse images of open sets along a continuous map is representably flat: the opens
of the target containing the image of a fixed open of the source are closed under finite
intersections and contain the whole space, and the category they form is thin. -/
instance representablyFlat_map {S T : TopCat.{u}} (g : S ⟶ T) :
    RepresentablyFlat (Opens.map g) := by
  constructor
  intro V
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · intro A B
    exact ⟨StructuredArrow.mk (Y := A.right ⊓ B.right)
        (homOfLE (le_inf (leOfHom A.hom) (leOfHom B.hom))),
      StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _),
      StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _), trivial⟩
  · intro A B a b
    refine ⟨A, 𝟙 A, ?_⟩
    rw [show a = b from StructuredArrow.hom_ext a b (Subsingleton.elim _ _)]
  · exact ⟨StructuredArrow.mk (Y := ⊤) (homOfLE le_top)⟩

/-- Taking inverse images of open sets along a continuous map `g : S ⟶ T` is a morphism of
sites from the site of opens of `T` to the site of opens of `S`: it is continuous and
representably flat, so the induced pullback of sheaves of sets is exact. -/
theorem isMorphismOfSites_map {S T : TopCat.{u}} (g : S ⟶ T) :
    (Opens.map g).IsMorphismOfSites
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology S) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

end TopologicalSpace.Opens

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of a morphism of schemes, read as a morphism of
sheaves of commutative rings into the restriction of `𝒪_X` along the inverse image of opens. -/
noncomputable def zariskiSharp :
    Y.zariskiRingedTopos.O ⟶
      ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)).obj X.sheaf :=
  ObjectProperty.homMk f.c

/-- A morphism of schemes read as a morphism of the Zariski ringed topoi `(X_Zar, 𝒪_X)` and
`(Y_Zar, 𝒪_Y)`: the morphism of topoi induced by the inverse image of opens, together with the
structure map `f♯`. -/
noncomputable def zariskiRingedToposHom :
    RingedToposHom X.zariskiRingedTopos Y.zariskiRingedTopos where
  toToposHom := (Opens.isMorphismOfSites_map f.base).morphismOfTopoi
  fSharp := zariskiSharp f ≫ (restrictionCommRingIso
    (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)
    (Opens.map f.base) X.sheaf).inv

/-- **Stacks 08T2.** The cotangent complex `L_{X/Y}` of a morphism of schemes `f : X ⟶ Y`: the
cotangent complex of `f` read as a morphism of the Zariski ringed topoi of `X` and `Y`, a
complex of sheaves of `𝒪_X`-modules. -/
@[stacks 08T2]
noncomputable def cotangentComplex :
    CochainComplex
      (Sheaf.targetModules (Opens.grothendieckTopology ↥X) X.zariskiRingedTopos.O) ℤ :=
  (zariskiRingedToposHom f).cotangentComplex

/-- **Stacks 08T2.** The cotangent complex `L_{X/Y}` of a morphism of schemes, regarded as an
object of the derived category of sheaves of `𝒪_X`-modules. -/
@[stacks 08T2 "the derived object"]
noncomputable abbrev cotangentComplexDerived
    [HasDerivedCategory.{u} (Sheaf.targetModules (Opens.grothendieckTopology ↥X)
      X.zariskiRingedTopos.O)] :
    DerivedCategory
      (Sheaf.targetModules (Opens.grothendieckTopology ↥X) X.zariskiRingedTopos.O) :=
  DerivedCategory.Q.obj f.cotangentComplex

/-- The cotangent complex of a morphism of schemes vanishes in positive cohomological
degrees. -/
theorem cotangentComplex_isZero_pos (m : ℤ) (hm : 0 < m) :
    IsZero ((f.cotangentComplex).X m) :=
  (zariskiRingedToposHom f).cotangentComplex_isZero_pos m hm

end AlgebraicGeometry.Scheme.Hom

end
