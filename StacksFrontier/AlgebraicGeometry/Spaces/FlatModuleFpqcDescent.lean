module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent

/-!
# Flatness of a module over the base descends along an fpqc covering

Let `{f i : X i ⟶ Y}` be an fpqc covering of algebraic spaces over a scheme `S`, let
`g : Y ⟶ Z` be a morphism and let `G` be a quasi-coherent `𝒪_Y`-module.  If every inverse image
`f i ^* G` is flat over `Z` along `f i ≫ g`, then `G` is flat over `Z`.  This is Morphisms of
Spaces, Lemma 05VY, read along a jointly surjective flat family instead of a single surjective
flat morphism: the pointwise clause (1) of that lemma applies at every point of every member,
and the members cover the points of `Y`.

The second statement is the composition clause of Stacks 05VX read globally: a module flat over
`Y` is flat over `Z` along a flat morphism `Y ⟶ Z`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_of_isFpqcCovering_of_isFlatOver_modulePullback`: flatness
  over the base descends along an fpqc covering of the source.
* `AlgebraicGeometry.Space.isFlatOver_comp_of_isFlat`: flatness over `Y` composes with a flat
  morphism `Y ⟶ Z`.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness of a module over the base descends along an fpqc covering** (Stacks 05VY, along a
jointly surjective flat family).  If `{f i : X i ⟶ Y}` is an fpqc covering and the inverse image
of the quasi-coherent `𝒪_Y`-module `G` along every member is flat over `Z`, then `G` is flat over
`Z`.

At a geometric point `ȳ` of `Y` choose a member and a geometric point `x̄` of it above `ȳ`; the
member is flat at `x̄`, so clause (1) of Stacks 05VY transfers flatness at `x̄` of the inverse
image to flatness of `G` at the image of `x̄`, which is a geometric point over the same point of
`|Y|` as `ȳ`. -/
theorem isFlatOver_of_isFpqcCovering_of_isFlatOver_modulePullback {I : Type v}
    {Y Z : AlgebraicSpaces B S hS} {X : I → AlgebraicSpaces B S hS} (f : ∀ i, X i ⟶ Y)
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite]
    (h : ∀ i, IsFlatOver B S hS (X i).2 (f i ≫ g).hom ((modulePullback B S hS (f i)).obj G)) :
    IsFlatOver B S hS Y.2 g.hom G := by
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS g G]
  intro ybar
  obtain ⟨i, x, hx⟩ :=
    jointly_surjective_points_of_fpqcCovering B S hS (fun i => (f i).hom) hf ybar.image
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS (X i).1 x
  have : ((modulePullback B S hS (f i)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) G inferInstance
  have hkey : IsFlatOverAtGeometricPoint B S hS g G (geometricPointMap (f i).hom xbar) :=
    (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS (f i) g G xbar
      (isFlatAt_of_isFlat B S hS (f i).hom (hf.1 i) xbar.image)).mpr
      ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (f i ≫ g) _).1 (h i) xbar)
  rw [← mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS g G
    (geometricPointMap (f i).hom xbar)] at hkey
  rw [← mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS g G ybar]
  rwa [geometricPointMap_image (f i).hom xbar, hx] at hkey

/-- **Flatness over the base composes with a flat morphism** (Stacks 05VX, part (1), at every
point).  A quasi-coherent `𝒪_X`-module flat over `Y` is flat over `Z` along `f ≫ g` when
`g : Y ⟶ Z` is flat. -/
theorem isFlatOver_comp_of_isFlat {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hF : IsFlatOver B S hS X.2 f.hom F) (hg : IsFlat B S hS g.hom) :
    IsFlatOver B S hS X.2 (f ≫ g).hom F := by
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f F] at hF
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (f ≫ g) F]
  exact fun xbar => isFlatOverAtGeometricPoint_comp B S hS f g F xbar (hF xbar)
    (isFlatAt_of_isFlat B S hS g.hom hg _)

end AlgebraicGeometry.Space

end
