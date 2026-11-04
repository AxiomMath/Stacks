module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion

/-!
# `f^!` through a factorization into a closed immersion, an open immersion and a proper morphism

Let `f : X ⟶ Y` be a morphism of `FTS S` over a Noetherian `S` which factors as a closed
immersion `i : X ⟶ W`, an open immersion `u : W ⟶ P` and a proper morphism `g : P ⟶ Y`. For
every compactification `j` of `f` and `K ∈ D⁺_QCoh(𝒪_Y)`, `f^!K ≅ a_i(Lu^*(a_g(K)))`, with `a_i`,
`a_g` the twisted inverse images of [Stacks, Tag 0A9E].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {W P : Scheme.{u}} (i : X.left ⟶ W) (u : W ⟶ P) (g : P ⟶ Y.left) [IsClosedImmersion i]
  [IsOpenImmersion u] [IsProper g] (hf : i ≫ u ≫ g = f.left)

namespace ClosedOpenProperFactorization

/-- `P` as an object of `FTS S`. -/
abbrev properFTS : FTS S := FTS.mk (g ≫ Y.hom)

/-- `W` as an object of `FTS S`. -/
abbrev openFTS : FTS S :=
  haveI : IsNoetherian P := isNoetherian_of_isProper g
  FTS.mk (u ≫ g ≫ Y.hom)

/-- `g` as a morphism of `FTS S`. -/
abbrev properHom : properFTS g ⟶ Y := MorphismProperty.Over.homMk g rfl

/-- `u ≫ g` as a morphism of `FTS S`. -/
abbrev openHom : openFTS u g ⟶ Y := MorphismProperty.Over.homMk (u ≫ g) rfl

/-- `i` as a morphism of `FTS S`. -/
abbrev closedHom : X ⟶ openFTS u g :=
  MorphismProperty.Over.homMk i (by
    change i ≫ u ≫ g ≫ Y.hom = X.hom
    rw [← Category.assoc, ← Category.assoc, Category.assoc i, hf]
    exact Over.w f.toCommaMorphism)

omit [IsClosedImmersion i] in
/-- The composite of `closedHom` and `openHom` in `FTS S` is `f`. -/
theorem closedHom_comp_openHom : closedHom f i u g hf ≫ openHom u g = f := by
  ext1
  exact hf

/-- The compactification `W ⊆ P` of `u ≫ g`. -/
def openCompactification : CompactificationOf (Over.mk (openHom u g).left) :=
  ⟨StructuredArrow.mk (Y := Over.mk g) (Over.homMk u rfl),
    ⟨inferInstanceAs (IsOpenImmersion u), inferInstanceAs (IsProper g)⟩⟩

variable (j : CompactificationOf (Over.mk f.left))

/-- **`f^! ≅ i^! ∘ (u ≫ g)^!` on `D⁺_QCoh`**, for any compactification `j` of `f`, with `i` and
`u ≫ g` compactified by `X` itself and by `W ⊆ P`. -/
def upperShriekPlusIso :
    haveI : IsProper (closedHom f i u g hf).left := inferInstanceAs (IsProper i)
    upperShriekPlus f j ≅ upperShriekPlus (openHom u g) (openCompactification u g) ⋙
      upperShriekPlus (closedHom f i u g hf) (properCompactification (closedHom f i u g hf)) :=
  haveI : IsProper (closedHom f i u g hf).left := inferInstanceAs (IsProper i)
  upperShriekPlusCongr (closedHom_comp_openHom f i u g hf).symm j
      ((closedHom_comp_openHom f i u g hf).symm ▸ j) ≪≫
    upperShriekCompIso _ _ _ _ _

/-- **`f^!K ≅ a_i(Lu^*(a_g(K)))`** for `K ∈ D⁺_QCoh(𝒪_Y)` and any compactification `j` of `f`. -/
def upperShriekObjIso (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : IsNoetherian P := isNoetherian_of_isProper g
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace u
    haveI : QuasiSeparatedSpace W := u.isOpenEmbedding.quasiSeparatedSpace
    (upperShriek f j).obj K ≅
      (twistedInverseImage i (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).obj
        ((quasiCoherentDerivedPullback' u).obj
          ((twistedInverseImage g
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K)) :=
  haveI : IsNoetherian P := isNoetherian_of_isProper g
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace u
  haveI : QuasiSeparatedSpace W := u.isOpenEmbedding.quasiSeparatedSpace
  haveI : IsProper (closedHom f i u g hf).left := inferInstanceAs (IsProper i)
  ((upperShriekPlusIso f i u g hf j).app ⟨K, hK⟩ : _) |> (ObjectProperty.ι _).mapIso |>
    fun e => e ≪≫ (upperShriekProperIso (closedHom f i u g hf)).app _

end ClosedOpenProperFactorization

end Stacks.Duality
