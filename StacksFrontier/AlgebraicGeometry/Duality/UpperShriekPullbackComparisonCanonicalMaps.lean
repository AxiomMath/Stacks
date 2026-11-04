module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# The maps `μ_{f,K}` of Tag 0B6T at the library's comparison maps

`Stacks.Duality.upperShriekCompareWithPullback` is the map
`μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` of [Stacks, Tag 0B6T] for given parameters: the comparison of
[Stacks, Tag 079U] for `f̄` and for `j.immersion`, the invertibility of the projection formula,
and a right unitor of the derived tensor product. Each of these is available in the library:
the comparison of [Stacks, Tag 079U] is `Stacks.Duality.quasiCoherentDerivedPullbackTensorIso`,
the right unitor is `Stacks.Duality.quasiCoherentDerivedTensorRightUnitor`, and the projection
formula of [Stacks, Tag 08EU] is the instance `Stacks.Duality.isIso_projectionFormulaMap_of_qcqs`.
This file states `μ_{f,K}` with those, so that it depends on `f`, the compactification `j` and
`K` only.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPullbackCompactificationIsoOfComp` — `Lf^* ≅ Lj^* ∘ Lf̄^*`
  on `D_QCoh`, from the composition isomorphism of derived pullbacks on `D_QCoh`.
* `Stacks.Duality.upperShriekCompareWithPullbackCanonical` — the maps `μ_{f,K}`.

## Main results

* `Stacks.Duality.upperShriekCompareWithPullbackCanonical_naturality` — `μ_{f,K}` is natural in
  `K`.

## References

* [Stacks Project, Tag 0B6T](https://stacks.math.columbia.edu/tag/0B6T)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

/-! ### The comparison map of Equation 48.8.0.1 restricted to `X` -/

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The composition formula for derived pullback along a compactification**:
`Lf̄^* ⋙ Lj^* ≅ Lf^*` on the quasi-coherent derived categories. It is
`Stacks.Duality.quasiCoherentDerivedPullbackCompIso` for the two morphisms of the
compactification, followed by the identification `Stacks.Duality.quasiCoherentDerivedPullbackCongr`
of `L(j.immersion ≫ f̄)^*` with `Lf^*` coming from `Stacks.Duality.immersion_comp_toBase`. -/
public def quasiCoherentDerivedPullbackCompactificationIsoOfComp :
    quasiCoherentDerivedPullback' j.toBase ⋙
        quasiCoherentDerivedPullback' j.immersion ≅
      quasiCoherentDerivedPullback' f.left :=
  quasiCoherentDerivedPullbackCompIso j.immersion j.toBase ≪≫
    quasiCoherentDerivedPullbackCongr (immersion_comp_toBase f j)

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- **Stacks Project, Tag 0B6T (Lemma 48.16.5).** Let `f : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S` and let `j` be a compactification of `X` over `Y`, with ambient scheme
`X̄`, open immersion `j.immersion` and proper structure morphism `f̄ = j.toBase`. The map

  `μ_{f,K} : Lf^*K ⊗ᴸ_{𝒪_X} f^!𝒪_Y ⟶ f^!K`

is the restriction to `X` of the comparison map `Lf̄^*K ⊗ᴸ_{𝒪_X̄} ā(𝒪_Y) ⟶ ā(K)` of Equation
48.8.0.1 ([Stacks, Tag 0A9S]), the source being read through the composition formula
`Lf^* ≅ Lf̄^* ⋙ Lj^*` and the monoidality of `Lj^*` of [Stacks, Tag 079U]. -/
@[stacks 0B6T "the maps μ_{f,K}"]
public def upperShriekCompareWithPullbackCanonical (K : quasiCoherentDerivedCategory Y.left) :
    ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
        ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ⟶
      (upperShriek f j).obj K :=
  ((quasiCoherentDerivedTensor X.left).map
        ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f j).inv.app
          K)).app
      ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
    (quasiCoherentDerivedPullbackTensorIso j.immersion).inv.app ((twistedInverseImage j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj
          (derivedStructureSheaf Y.left),
      (quasiCoherentDerivedPullback' j.toBase).obj K) ≫
    (quasiCoherentDerivedPullback' j.immersion).map
      (twistedInverseImageCompareWithPullback j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)
        (quasiCoherentDerivedPullbackTensorIso j.toBase).hom
        (quasiCoherentDerivedTensorRightUnitor Y.left) K)

/-- **The map `μ_{f,K}` of [Stacks, Tag 0B6T] is functorial in `K`.** Each of its three factors
is natural: the composition formula for derived pullback, the monoidality of `Lj^*`, and
Equation 48.8.0.1 by `Stacks.Duality.compareWithPullback_naturality`. -/
@[stacks 0B6T "functoriality of μ_{f,K} in K"]
public theorem upperShriekCompareWithPullbackCanonical_naturality
    {K K' : quasiCoherentDerivedCategory Y.left} (h : K ⟶ K') :
    ((quasiCoherentDerivedTensor X.left).map
          ((quasiCoherentDerivedPullback' f.left).map h)).app
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
        upperShriekCompareWithPullbackCanonical f j K' =
      upperShriekCompareWithPullbackCanonical f j K ≫
        (upperShriek f j).map h := by
  have hq := isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase
  have paste : ∀ {X₁ X₂ X₃ X₄ X₅ Z₃ Z₄ Z₅ : quasiCoherentDerivedCategory X.left}
      (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅)
      (a' : X₁ ⟶ Z₃) (u : Z₃ ⟶ X₃) (c' : Z₃ ⟶ Z₄) (v : Z₄ ⟶ X₄)
      (e : Z₄ ⟶ Z₅) (g : Z₅ ⟶ X₅), a ≫ b = a' ≫ u → u ≫ c = c' ≫ v → v ≫ d = e ≫ g →
      a ≫ b ≫ c ≫ d = (a' ≫ c' ≫ e) ≫ g := by
    intro X₁ X₂ X₃ X₄ X₅ Z₃ Z₄ Z₅ a b c d a' u c' v e g h₁ h₂ h₃
    simp only [Category.assoc]
    rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  have hκ :=
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f j).inv.naturality h
  have hα := (quasiCoherentDerivedPullbackTensorIso j.immersion).inv.naturality
    (((𝟙 ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left))),
      (quasiCoherentDerivedPullback' j.toBase).map h) :
      ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
        (quasiCoherentDerivedPullback' j.toBase).obj K) ⟶
      ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
        (quasiCoherentDerivedPullback' j.toBase).obj K'))
  have hc := compareWithPullback_naturality j.toBase hq
    (quasiCoherentDerivedPullbackTensorIso j.toBase).hom
    (twistedInverseImageAdjunction j.toBase hq) (quasiCoherentDerivedTensorRightUnitor Y.left) h
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Prod.swap_map,
    Functor.uncurry_obj_map, CategoryTheory.Prod.swap_obj, Functor.prod_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] at hα
  have hα2 :
      ((quasiCoherentDerivedTensor X.left).map
            ((quasiCoherentDerivedPullback' j.immersion).map
              ((quasiCoherentDerivedPullback' j.toBase).map h))).app
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
        (quasiCoherentDerivedPullbackTensorIso j.immersion).inv.app
          ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
            (quasiCoherentDerivedPullback' j.toBase).obj K') =
      (quasiCoherentDerivedPullbackTensorIso j.immersion).inv.app
          ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
            (quasiCoherentDerivedPullback' j.toBase).obj K) ≫
        (quasiCoherentDerivedPullback' j.immersion).map
          (((quasiCoherentDerivedTensor j.space).map
              ((quasiCoherentDerivedPullback' j.toBase).map h)).app
            ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left))) :=
    hα
  have h1 := congrArg (fun z => ((quasiCoherentDerivedTensor X.left).map z).app
    ((upperShriek f j).obj (derivedStructureSheaf Y.left))) hκ
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.comp_map] at h1
  have h3 := congrArg (quasiCoherentDerivedPullback' j.immersion).map hc
  simp only [Functor.map_comp] at h3
  simp only [upperShriekCompareWithPullbackCanonical, upperShriek_map f j h]
  exact paste _ _ _ _ _ _ _ _ _ _ h1 hα2 h3

end Stacks.Duality

end
