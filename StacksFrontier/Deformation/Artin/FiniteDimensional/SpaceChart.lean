module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource

/-!
# A scheme chart of an algebraic space smooth over a scheme locally of finite type

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S` which is representable by
an algebraic space, with a smooth 1-morphism `𝒴 ⟶ (Sch/V)` to the category of a scheme `V`
locally of finite type over `S`. An étale scheme atlas `W ⟶ 𝒴` of the representing algebraic
space gives a 1-morphism `(Sch/W) ⟶ 𝒴` which is representable by algebraic spaces with
surjective and smooth base changes, and `W` is again locally of finite type over `S`, the
composite `W ⟶ V` being smooth.

## References

* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A scheme chart of an algebraic space smooth over a scheme locally of finite type.**  If `𝒴`
is representable by an algebraic space and has a smooth 1-morphism to `(Sch/V)` with `V` locally of
finite type over `S`, then there is a scheme `W` locally of finite type over `S` and a 1-morphism
`(Sch/W) ⟶ 𝒴`, representable by algebraic spaces, whose base changes are surjective and
smooth. -/
theorem exists_smoothChart_of_isRepresentableByAlgebraicSpace
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒴 : IsRepresentableByAlgebraicSpace B S hS 𝒴)
    (V : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (π : 𝒴 ⟶ schemeFibredCategory B S hS V) (hπ : IsRelativelySmooth B S hS π) :
    ∃ (W : BigFppfOver B S hS) (_ : LocallyOfFiniteType (B.inclusion.map W.hom))
      (k : schemeFibredCategory B S hS W ⟶ 𝒴)
      (hk : IsRepresentableByAlgebraicSpaces B S hS k.hom),
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS) k hk ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) k hk := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := h𝒴
  obtain ⟨W, atl, hsurj, hsm⟩ := Space.exists_isSurjective_isSmooth_atlas B S hS hF
  let eW := CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver W
  obtain ⟨k, hk⟩ := exists_oneMorphism_representingMap_eq' B S hS
    (schemeFibredCategory B S hS W) 𝒴 (yoneda.obj W) F eW eF atl
  have hkrep : IsRepresentableByAlgebraicSpaces B S hS k.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS k
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) ⟨F, hF, ⟨eF⟩⟩
  have hkS : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) k hkrep :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) k hkrep (yoneda.obj W) F
      (isAlgebraicSpace_yoneda B S hS W) hF eW eF).2 (by
        change Space.IsSurjective B S hS _
        rwa [hk])
  have hkM : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) k hkrep :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) k hkrep (yoneda.obj W) F
      (isAlgebraicSpace_yoneda B S hS W) hF eW eF).2 (by
        change Space.IsSmooth B S hS _
        rwa [hk])
  have hc : IsRelativelySmooth B S hS (k ≫ π) :=
    isRelativelySmooth_comp B S hS k π ⟨hkrep, hkM⟩ hπ
  let eV := CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver V
  have hrep := (isRelativelySmooth_iff_isSmooth_representingMap B S hS (k ≫ π) hc.1
    (yoneda.obj W) (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS V) eW eV).1 hc
  set g := representingMap B S hS (schemeFibredCategory B S hS W)
    (schemeFibredCategory B S hS V) (yoneda.obj W) (yoneda.obj V) eW eV (k ≫ π) with hg
  rw [← yoneda.map_preimage g] at hrep
  have hsmooth : Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage g)) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS Smooth.isEtaleLocalOnSourceAndTarget
      (yoneda.preimage g)).1 hrep
  have hw : B.inclusion.map W.hom =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage g) ≫ B.inclusion.map V.hom := by
    rw [← Over.w (yoneda.preimage g), Functor.map_comp]
    rfl
  refine ⟨W, ?_, k, hkrep, hkS, hkM⟩
  rw [hw]
  infer_instance

end AlgebraicGeometry.Stack
