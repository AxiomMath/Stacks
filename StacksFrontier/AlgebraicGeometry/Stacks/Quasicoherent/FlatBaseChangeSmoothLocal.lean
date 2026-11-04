module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# The smooth-local criterion for `LQCoh^fbc` (Stacks 07AQ, part (1))

Let `𝒳` be an algebraic stack over `S`. A sheaf of `𝒪_𝒳`-modules on `𝒳_étale` lies in
`LQCoh^fbc(𝒪_𝒳)` when it is locally quasi-coherent (**Stacks 06WJ**) and has the flat base
change property (**Stacks 0762**). **Stacks 07AQ** part (1) says that this condition is local
for a jointly surjective family of smooth 1-morphisms `f j : 𝒵 j ⟶ 𝒳`: if each inverse image
`f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`. The source
proves it by combining the same criterion for local quasi-coherence, **Stacks 075Y**, with the
same criterion for the flat base change property, **Stacks 0764** part (3).

The local quasi-coherence half is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`. The flat base
change half is taken as a hypothesis here, and the implementation notes record why: the flat base
change property as formalized asks the *presheaf*-level inverse image to compare isomorphically,
and the source's argument for its locality is an argument about étale sheaves.

## Main definitions

* `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`: membership in
  `LQCoh^fbc(𝒪_𝒳)`, the conjunction of **Stacks 06WJ** and **Stacks 0762**.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules`: the category
  `LQCoh^fbc(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_modulePullback_restrictModuleToSmallEtale`: a module with the
  flat base change property has, below every arrow lying over a flat morphism of schemes, an
  inverse image of its restriction which is already a sheaf on the small étale site.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_of_isSmooth_jointlySurjective`:
  **Stacks 07AQ** part (1), with the flat base change property of `F` as a hypothesis.

## Implementation notes

The comparison map of **Stacks 06WC** has for its source the inverse image of the restriction
computed in presheaves of modules, `PresheafOfModules.pullback` being the left adjoint of the
direct image on presheaves; no sheafification enters, and for an arrow lying over a morphism of
schemes which is not étale that left adjoint is a left Kan extension and carries no sheaf
condition. The source of **Stacks 0764** part (3) argues instead with the inverse image of étale
*sheaves* of modules: it produces an étale covering `{U_i → U}` of the scheme below the source of
the arrow over whose members the arrow lifts through one member of the family, identifies the
comparison map over each `U_i` with the comparison map of the lift by **Stacks 075D** part (3),
and concludes because a map of étale sheaves which is an isomorphism over a covering is an
isomorphism. That last step asks the source of the comparison map to be an étale sheaf, which
the presheaf-level inverse image is not; and the sheaf condition is not itself local, so knowing
that the source becomes a sheaf over each `U_i` does not supply it over `U`.

What the flat base change property does give is the converse implication, recorded here as
`AlgebraicGeometry.Stack.isSheaf_modulePullback_restrictModuleToSmallEtale`: a module with the
property has presheaf-level inverse images that are sheaves, because they are isomorphic to
restrictions of the module itself. So the hypothesis `hfbc` below is the only gap between this
statement and the source's part (1), and it is a gap about the two readings of the inverse image
rather than about the geometry of the family.

Joint surjectivity is expressed with the points of **Stacks 04XG**, in the spelling
`Set.univ = ⋃ j, Set.range (|f j|)` already used for **Stacks 075Y** and **Stacks 07AN**. The
module universe is pinned to the universe of the schemes throughout, as the comparison map of
**Stacks 06WC** pins it.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Membership in `LQCoh^fbc(𝒪_𝒳)`: a presheaf of modules over the structure sheaf of a category
fibred in groupoids which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base
change property (**Stacks 0762**) for the étale topology. -/
noncomputable abbrev IsLocallyQuasicoherentWithFlatBaseChange {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :
    Prop :=
  IsLocallyQuasicoherent B E h S hS p hp F ∧
    HasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F

/-- The category `LQCoh^fbc(𝒪_𝒳)`: the full subcategory of the étale sheaves of `𝒪_𝒳`-modules
whose underlying presheaf is locally quasi-coherent and has the flat base change property. This
is the category **Stacks 07AQ** is about. -/
noncomputable abbrev locallyQuasicoherentFlatBaseChangeModules {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :=
  ObjectProperty.FullSubcategory
    (fun F : SheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) =>
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F.val)

/-- For a module with the flat base change property of **Stacks 0762** which is a sheaf for the
étale topology, the inverse image below an arrow lying over a flat morphism of schemes of the
restriction at the arrow's target is a sheaf on the small étale site of the scheme below the
arrow's source.

The comparison map of **Stacks 06WC** identifies that inverse image with the restriction at the
arrow's source, which is a sheaf by
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale_isSheaf`. -/
theorem isSheaf_modulePullback_restrictModuleToSmallEtale {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hfbc : HasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F)
    {x y : 𝒳} (φ : x ⟶ y) (hflat : Flat (B.inclusion.map (p.map φ).left)) :
    Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.pullback.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).obj
        (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B) F)).presheaf := by
  have hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B) F) := hfbc φ hflat
  exact (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso
    (asIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)))).2
    (restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF)

/-- **Stacks 07AQ, part (1), the local quasi-coherence half.** Let `f j : 𝒵 j ⟶ 𝒳` be a family
of smooth 1-morphisms of algebraic stacks over `S` with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F`
be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. If every inverse image `f j^{-1} F` lies in
`LQCoh^fbc(𝒪_{𝒵 j})` and `F` has the flat base change property, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`.

Local quasi-coherence of `F` is **Stacks 075Y**, applied to the local quasi-coherence of the
inverse images. The flat base change property of `F` is the hypothesis `hfbc`: the source deduces
it from **Stacks 0764** part (3), whose argument is not available for the presheaf-level inverse
image that the flat base change property is formulated with here; see the implementation notes of
this file. -/
@[stacks 07AQ "part (1), the local quasi-coherence half: the criterion along a jointly \
  surjective family of smooth morphisms, with the flat base change property of the source \
  assumed (Stacks 0764 part (3))"]
theorem isLocallyQuasicoherentWithFlatBaseChange_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F)
    (hlqc : ∀ j, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F)) :
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      F :=
  ⟨isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F hF
    fun j => (hlqc j).1, hfbc⟩

end AlgebraicGeometry.Stack

end

