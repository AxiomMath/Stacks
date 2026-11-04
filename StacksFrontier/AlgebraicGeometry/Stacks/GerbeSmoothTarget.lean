module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# Smoothness descends from a gerbe to the algebraic space it lies over

Let `π : 𝒳 ⟶ F` make an algebraic stack `𝒳` over `S` a gerbe over an algebraic space `F`
(Stacks 06QC), and let `q : F ⟶ G` be a morphism of algebraic spaces. If the composite
`𝒳 ⟶ F ⟶ G` is smooth, then so is `q`.

This is the argument of the proof of Stacks 0DPK with the Picard stack replaced by an arbitrary
gerbe: by Stacks 0DN8 the gerbe `π` is surjective and smooth; if `U ⟶ 𝒳` is a smooth surjection
from an algebraic space, then `U ⟶ F` is a smooth surjection (Stacks 075V, 04ZT) and `U ⟶ G` is
smooth (Stacks 075V), so `q` is smooth by Stacks 0AHD. The last step is performed at the level of
algebraic stacks, by `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_surjective`, and
read back on `q` by the forward half of Stacks 06FM for representable source and target.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isGerbeOver_of_isSmooth_comp`: the
  descent of smoothness from a gerbe.

No declaration here carries a tag: the second result is the general form of the proof of
Stacks 0DPK, whose statement is about the Picard functor.

## References

* [Stacks Project, Tag 0DPK](https://stacks.math.columbia.edu/tag/0DPK)
* [Stacks Project, Tag 0DN8](https://stacks.math.columbia.edu/tag/0DN8)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Smoothness descends from a gerbe to the algebraic space it lies over.** Let `𝒳` be an
algebraic stack over `S`, let `π : 𝒳 ⟶ F` make `𝒳` a gerbe over an algebraic space `F`
(Stacks 06QC), and let `q : F ⟶ G` be a morphism of algebraic spaces over `S`. If the
composite `𝒳 ⟶ F ⟶ G` is smooth (Stacks 075U), then `q` is smooth.

This is the proof of Stacks 0DPK for an arbitrary gerbe. Choose a smooth presentation
`a : U ⟶ 𝒳`, surjective, by an algebraic space. By Stacks 0DN8 the gerbe `π` is surjective and
smooth, so `a ≫ π : U ⟶ F` is surjective and smooth (Stacks 04ZT, 075V), and it is representable
since its source is an algebraic space; and `a ≫ (π ≫ q)` is smooth (Stacks 075V). So `q` is
smooth as a 1-morphism of algebraic stacks by the stack-level form of Stacks 0AHD, and hence as a
morphism of algebraic spaces by Stacks 06FM for representable source and target. -/
theorem isSmooth_of_isGerbeOver_of_isSmooth_comp {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS F hF) (hπ : IsGerbeOver B S hS π)
    (q : F ⟶ G)
    (hsm : IsSmooth B S hS (π ≫ algebraicSpaceStackMap.{u, w} B S hS hF hG q)) :
    Space.IsSmooth B S hS q := by
  obtain ⟨V, hV, a, hasm, hasu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒳.property
  let a' : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom a
  have ha'sm : IsSmooth B S hS a' :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (algebraicSpaceStack.{u, w} B S hS V hV).property 𝒳.property a'.hom hasm.1).2 hasm.2
  have ha'su : Stack.IsSurjective B S hS a' :=
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS a' hasu
  obtain ⟨hπsu, hπsm⟩ := isSurjective_and_isSmooth_of_isGerbeOver B S hS π hπ
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (a' ≫ π).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, w} B S hS F hF).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV) _
  have hstack : IsSmooth B S hS (algebraicSpaceStackMap.{u, w} B S hS hF hG q) :=
    isSmooth_of_comp_surjective B S hS (a' ≫ π) _ hrep (isSmooth_comp B S hS a' π ha'sm hπsm)
      (Stack.isSurjective_comp B S hS a' π ha'su hπsu)
      (isSmooth_of_twoIso B S hS (Bicategory.associator a' π _).symm
        (isSmooth_comp B S hS a' _ ha'sm hsm))
  have h := isSmooth_representingMap_of_isSmooth.{u, w} B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) F G hF hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ hstack
  rwa [representingMap_associatedMap] at h

/-- **Smoothness descends from a gerbe, for any 1-morphism to the target.** Let `π : 𝒳 ⟶ F` make
the algebraic stack `𝒳` a gerbe over the algebraic space `F`, let `ρ : 𝒳 ⟶ G` be a smooth
1-morphism to an algebraic space `G`, and let `q : F ⟶ G` be a morphism of algebraic spaces with
`π ≫ q` 2-isomorphic to `ρ`. Then `q` is smooth. -/
theorem isSmooth_of_isGerbeOver_of_twoIso {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS F hF) (hπ : IsGerbeOver B S hS π)
    (ρ : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS G hG) (hρ : IsSmooth B S hS ρ)
    (q : F ⟶ G) (e : π ≫ algebraicSpaceStackMap.{u, w} B S hS hF hG q ≅ ρ) :
    Space.IsSmooth B S hS q :=
  isSmooth_of_isGerbeOver_of_isSmooth_comp B S hS hF hG π hπ q
    (isSmooth_of_twoIso B S hS e.symm hρ)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
