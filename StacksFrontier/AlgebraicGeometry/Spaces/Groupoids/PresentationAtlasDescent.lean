module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasFaithful

/-!
# Descent of morphisms of quasi-coherent modules along the atlas of a presentation

Let `X = U/R` be a presentation of an algebraic space with atlas `φ : U ⟶ X`, and let `G`, `H` be
quasi-coherent `𝒪_X`-modules.  The inverse images `φ^*G`, `φ^*H` carry their canonical transition
morphisms `t^*φ^*G ≅ s^*φ^*G` along the two projections `t, s : R ⟶ U` (`spaceBaseDescent`).  By
the equivalence of Stacks 03M3 between quasi-coherent `𝒪_X`-modules and quasi-coherent modules on
the presentation groupoid (`presentationQuasicoherentEquivalence`), a morphism `χ : φ^*G ⟶ φ^*H`
which carries the canonical transition morphism of `φ^*G` to that of `φ^*H` is the inverse image of
a unique morphism `G ⟶ H`.

Neither module is given by descent data on the atlas; compare
`existsUnique_presentationDescendedIntoHom`, where the target is a descended module.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `presentationAtlasGroupoidHom`: the morphism of quasi-coherent modules on the presentation
  groupoid given by `χ`.
* `presentationAtlasDescendedHom`: **the descended morphism `G ⟶ H`**.

## Main results

* `modulePullback_map_presentationAtlasDescendedHom`: its inverse image along the atlas is `χ`.
* `presentationAtlasDescendedHom_unique`: it is the only such morphism.
* `existsUnique_presentationAtlasDescendedHom`: **descent of a morphism of quasi-coherent modules
  along the atlas of a presentation.**

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {G H : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
  (χ : (modulePullback B S hS (presentationAtlas P)).obj G.obj ⟶
    (modulePullback B S hS (presentationAtlas P)).obj H.obj)
  (hχ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) G.obj)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) H.obj) χ)

/-- The morphism of quasi-coherent modules on the presentation groupoid given by a chart morphism
which carries the canonical transition morphisms to each other. -/
def presentationAtlasGroupoidHom :
    (presentationQuasicoherentEquivalence P).functor.obj G ⟶
      (presentationQuasicoherentEquivalence P).functor.obj H :=
  QuasicoherentModule.homMk χ ((presentationQuasicoherentEquivalence_compatible_iff P χ).2 hχ)

/-- **The descended morphism `G ⟶ H`**: the morphism of quasi-coherent `𝒪_X`-modules corresponding,
under the equivalence of Stacks 03M3, to the chart morphism `χ`. -/
def presentationAtlasDescendedHom : G.obj ⟶ H.obj :=
  ((presentationQuasicoherentEquivalence P).functor.preimage
    (presentationAtlasGroupoidHom P χ hχ)).hom

/-- **The inverse image along the atlas of the descended morphism is `χ`.** -/
theorem modulePullback_map_presentationAtlasDescendedHom :
    (modulePullback B S hS (presentationAtlas P)).map (presentationAtlasDescendedHom P χ hχ) = χ :=
  (presentationQuasicoherentEquivalence_functor_map_hom P _).symm.trans
    (congrArg QuasicoherentModule.Hom.hom
      ((presentationQuasicoherentEquivalence P).functor.map_preimage
        (presentationAtlasGroupoidHom P χ hχ)))

/-- **The descended morphism is unique**: a morphism `G ⟶ H` of quasi-coherent `𝒪_X`-modules whose
inverse image along the atlas is `χ` is the descended morphism. -/
theorem presentationAtlasDescendedHom_unique (g : G.obj ⟶ H.obj)
    (hg : (modulePullback B S hS (presentationAtlas P)).map g = χ) :
    g = presentationAtlasDescendedHom P χ hχ :=
  have := G.property
  have := H.property
  presentationAtlas_map_injective P
    (hg.trans (modulePullback_map_presentationAtlasDescendedHom P χ hχ).symm)

include hχ in
/-- **Descent of a morphism of quasi-coherent modules along the atlas of a presentation**
(Stacks 03M3).  Let `X = U/R` be a presentation of an algebraic space with atlas `φ : U ⟶ X` and
`G`, `H` quasi-coherent `𝒪_X`-modules.  A morphism `χ : φ^*G ⟶ φ^*H` which carries the canonical
transition morphism of `φ^*G` to that of `φ^*H` is the inverse image along the atlas of a unique
morphism `G ⟶ H`. -/
theorem existsUnique_presentationAtlasDescendedHom :
    ∃! g : G.obj ⟶ H.obj, (modulePullback B S hS (presentationAtlas P)).map g = χ :=
  ⟨presentationAtlasDescendedHom P χ hχ, modulePullback_map_presentationAtlasDescendedHom P χ hχ,
    presentationAtlasDescendedHom_unique P χ hχ⟩

end AlgebraicGeometry.Space

end
