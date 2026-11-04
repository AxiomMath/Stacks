module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# The comparison map from the derived pullback to the upper shriek functor

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`, the category
of schemes separated and of finite type over `S` of [Stacks, Tag 0F42]. Let `j` be a
compactification of `X` over `Y`, with ambient scheme `X̄ = j.space`, open immersion
`j.immersion : X ⟶ X̄` and proper structure morphism `f̄ = j.toBase : X̄ ⟶ Y`, and let
`ā = Stacks.Duality.twistedInverseImage` be the right adjoint of `Rf̄_*`, so that
`f^! = j^* ∘ ā` is `Stacks.Duality.upperShriek`. [Stacks, Tag 0B6T] (Lemma 48.16.5) constructs
maps

  `μ_{f,K} : Lf^*K ⊗ᴸ_{𝒪_X} f^!𝒪_Y ⟶ f^!K`,

functorial in `K`, by restricting to `X` the comparison map of Equation 48.8.0.1,

  `Lf̄^*K ⊗ᴸ_{𝒪_X̄} ā(𝒪_Y) ⟶ ā(K)`,

of [Stacks, Tag 0A9S]. This file performs that construction: `μ_{f,K}` is `Lj^*` applied to
Equation 48.8.0.1, read on the source through `Lf^* ≅ Lf̄^* ⋙ Lj^*` and the monoidality of `Lj^*`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `derivedPullbackMapEqIso` — equal morphisms of schemes have equal derived pullbacks.
* `quasiCoherentDerivedPullbackCompactificationIso` — `Lf̄^* ⋙ Lj^* ≅ Lf^*` on the quasi-coherent
  derived categories, the composition formula at the factorisation `f = j.immersion ≫ f̄` of the
  compactification.
* `upperShriekCompareWithPullback` — **[Stacks, Tag 0B6T]**, the map `μ_{f,K}`.

## Main results

* `upperShriek_map` — `f^!` acts on morphisms as `Lj^*` of `ā`, by definition of the composite.
* `upperShriekCompareWithPullback_naturality` — `μ_{f,K}` is functorial in `K`.

## Implementation notes

*What the construction is.* The three factors of `μ_{f,K}` are the three steps of the source's
one-line construction. Tensoring the inverse of
`quasiCoherentDerivedPullbackCompactificationIso` with the identity of `f^!𝒪_Y` rewrites the
source `Lf^*K ⊗ᴸ f^!𝒪_Y` as `Lj^*(Lf̄^*K) ⊗ᴸ Lj^*(ā𝒪_Y)`; the inverse of the monoidality
isomorphism of `Lj^*` turns that into `Lj^*(Lf̄^*K ⊗ᴸ ā𝒪_Y)`; and `Lj^*` applied to Equation
48.8.0.1 for `f̄` lands in `Lj^*(āK)`, which is `f^!K` by definition of
`Stacks.Duality.upperShriek`. Nothing is chosen from an existence statement: every factor is a
named morphism of this repository.

*The parameters.* Besides the compactification `j`, whose existence is [Stacks, Tag 0F41], they
are the parameters of `Stacks.Duality.twistedInverseImageCompareWithPullback`
([Stacks, Tag 0A9S]): the comparison `αBar` of [Stacks, Tag 079U] for `f̄` and the invertibility
`hproj` of the projection formula of [Stacks, Tag 0B53], which is what Equation 48.8.0.1 is built
from, and the right unitor `ρ` of the derived tensor product, which this repository's derived
tensor product does not carry. The quasi-coherence inputs of [Stacks, Tag 08D5] and
[Stacks, Tag 08DW] for the four functors `Rf̄_*`, `Lj^*`, `Lf̄^*`, `Lf^*` and the right adjoint of
[Stacks, Tag 0A9E] are theorems and are not carried.

*Why `αImm` is an isomorphism and `αBar` a morphism.* Both are the comparison of
[Stacks, Tag 079U], for `j.immersion` and for `f̄`. Tag 079U asserts that it is an isomorphism,
and the construction of `μ_{f,K}` uses it in the direction `Lj^*A ⊗ᴸ Lj^*B ⟶ Lj^*(A ⊗ᴸ B)`, so
for `j.immersion` it enters as the isomorphism the tag provides. Equation 48.8.0.1 uses it only in
the forward direction, so for `f̄` the morphism form of
`Stacks.Duality.compareWithPullbackTensor` is what is needed. The library proves Tag 079U at
`CategoryTheory.HasDerivedCategory.standard`
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`), while `f^!` lives at the
locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and
`HasDerivedCategory` carries the localization as data, so the two statements do not transport.

*What is not here.* The source's lemma has a second half: for a second morphism `g : Y ⟶ Z` a
pentagon relating `μ_f`, `μ_g` and `μ_{g ∘ f}` commutes. It is stated through the isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX], which this repository does not have, so the
pentagon cannot be written down here. Likewise the source's verification that `μ_{f,K}` does not
depend on the compactification is a statement about the canonical isomorphisms of
[Stacks, Tag 0AA0], also absent; as with `Stacks.Duality.upperShriek` itself, the compactification
is an argument and the source's independence argument is what would let one suppress it.

## References

* [Stacks Project, Tag 0B6T](https://stacks.math.columbia.edu/tag/0B6T)
* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
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

/-! ### Derived pullback along equal morphisms -/

section Congr

variable {X Y : Scheme.{u}} {m m' : X ⟶ Y}

/-- Equal morphisms of schemes have equal derived pullbacks, hence canonically isomorphic ones.
This is what makes the two factorisations `f` and `j.immersion ≫ j.toBase` of the structure
morphism of a compactification interchangeable for `Lf^*`. -/
public def derivedPullbackMapEqIso (h : m = m') : derivedPullback m ≅ derivedPullback m' :=
  eqToIso (congrArg derivedPullback h)

end Congr

/-! ### The comparison map of Equation 48.8.0.1 restricted to `X` -/

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The composition formula for derived pullback along a compactification**:
`Lf̄^* ⋙ Lj^* ≅ Lf^*` on the quasi-coherent derived categories. It is
`Stacks.Duality.derivedPullbackCompIso` for the two morphisms of the compactification, followed by
the identification of `L(j.immersion ≫ f̄)^*` with `Lf^*` coming from
`Stacks.Duality.immersion_comp_toBase`, read on the full subcategories of complexes with
quasi-coherent cohomology. -/
public def quasiCoherentDerivedPullbackCompactificationIso :
    quasiCoherentDerivedPullback' j.toBase ⋙
        quasiCoherentDerivedPullback' j.immersion ≅
      quasiCoherentDerivedPullback' f.left :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((derivedPullbackCompIso j.immersion j.toBase ≪≫
        derivedPullbackMapEqIso (immersion_comp_toBase f j)).app K.obj))
    (fun e => ObjectProperty.hom_ext _
      ((derivedPullbackCompIso j.immersion j.toBase ≪≫
        derivedPullbackMapEqIso (immersion_comp_toBase f j)).hom.naturality e.hom))

variable [CompactSpace S] [QuasiSeparatedSpace S]
  (αBar : quasiCoherentDerivedTensorSwap Y.left ⋙
      quasiCoherentDerivedPullback' j.toBase ⟶
    (quasiCoherentDerivedPullback' j.toBase).prod
        (quasiCoherentDerivedPullback' j.toBase) ⋙
      quasiCoherentDerivedTensorSwap j.space)
  (αImm : quasiCoherentDerivedTensorSwap j.space ⋙
      quasiCoherentDerivedPullback' j.immersion ≅
    (quasiCoherentDerivedPullback' j.immersion).prod
        (quasiCoherentDerivedPullback' j.immersion) ⋙
      quasiCoherentDerivedTensorSwap X.left)
  [hproj : ∀ (E : quasiCoherentDerivedCategory j.space)
      (K : quasiCoherentDerivedCategory Y.left),
    IsIso (projectionFormulaMap j.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase) αBar E K)]
  (ρ : (quasiCoherentDerivedTensor Y.left).flip.obj (derivedStructureSheaf Y.left) ≅ 𝟭 _)

include hproj

/-- **Stacks Project, Tag 0B6T (Lemma 48.16.5).** Let `f : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S` and let `j` be a compactification of `X` over `Y`, with ambient scheme
`X̄`, open immersion `j.immersion` and proper structure morphism `f̄ = j.toBase`. The map

  `μ_{f,K} : Lf^*K ⊗ᴸ_{𝒪_X} f^!𝒪_Y ⟶ f^!K`

is the restriction to `X` of the comparison map `Lf̄^*K ⊗ᴸ_{𝒪_X̄} ā(𝒪_Y) ⟶ ā(K)` of Equation
48.8.0.1 ([Stacks, Tag 0A9S]), the source being read through the composition formula
`Lf^* ≅ Lf̄^* ⋙ Lj^*` and the monoidality of `Lj^*` of [Stacks, Tag 079U]. -/
@[stacks 0B6T "the map mu_{f,K} of Lemma 48.16.5, at the compactification j from which \
Stacks.Duality.upperShriek computes f^!"]
public def upperShriekCompareWithPullback (K : quasiCoherentDerivedCategory Y.left) :
    ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
        ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ⟶
      (upperShriek f j).obj K :=
  ((quasiCoherentDerivedTensor X.left).map
        ((quasiCoherentDerivedPullbackCompactificationIso f j).inv.app
          K)).app
      ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
    αImm.inv.app ((twistedInverseImage j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj
          (derivedStructureSheaf Y.left),
      (quasiCoherentDerivedPullback' j.toBase).obj K) ≫
    (quasiCoherentDerivedPullback' j.immersion).map
      (twistedInverseImageCompareWithPullback j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase) αBar ρ K)

omit hproj in
/-- `f^!` acts on a morphism as `Lj^*` applied to the action of `ā`, by definition of the
composite `f^! = j^* ∘ ā`. -/
public theorem upperShriek_map {K K' : quasiCoherentDerivedCategory Y.left} (h : K ⟶ K') :
    (upperShriek f j).map h =
      (quasiCoherentDerivedPullback' j.immersion).map
        ((twistedInverseImage j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).map h) :=
  rfl

/-- **The map `μ_{f,K}` of [Stacks, Tag 0B6T] is functorial in `K`.** Each of its three factors
is natural: the composition formula for derived pullback, the monoidality of `Lj^*`, and
Equation 48.8.0.1 by `Stacks.Duality.compareWithPullback_naturality`. -/
@[stacks 0B6T "functoriality of mu_{f,K} in K"]
public theorem upperShriekCompareWithPullback_naturality
    {K K' : quasiCoherentDerivedCategory Y.left} (h : K ⟶ K') :
    ((quasiCoherentDerivedTensor X.left).map
          ((quasiCoherentDerivedPullback' f.left).map h)).app
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
        upperShriekCompareWithPullback f j αBar αImm ρ K' =
      upperShriekCompareWithPullback f j αBar αImm ρ K ≫
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
    (quasiCoherentDerivedPullbackCompactificationIso f j).inv.naturality h
  have hα := αImm.inv.naturality
    (((𝟙 ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left))),
      (quasiCoherentDerivedPullback' j.toBase).map h) :
      ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
        (quasiCoherentDerivedPullback' j.toBase).obj K) ⟶
      ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
        (quasiCoherentDerivedPullback' j.toBase).obj K'))
  have hc := compareWithPullback_naturality j.toBase hq αBar
    (twistedInverseImageAdjunction j.toBase hq) ρ h
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Prod.swap_map,
    Functor.uncurry_obj_map, CategoryTheory.Prod.swap_obj, Functor.prod_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] at hα
  have hα2 :
      ((quasiCoherentDerivedTensor X.left).map
            ((quasiCoherentDerivedPullback' j.immersion).map
              ((quasiCoherentDerivedPullback' j.toBase).map h))).app
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
        αImm.inv.app
          ((twistedInverseImage j.toBase hq).obj (derivedStructureSheaf Y.left),
            (quasiCoherentDerivedPullback' j.toBase).obj K') =
      αImm.inv.app
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
  simp only [upperShriekCompareWithPullback, upperShriek_map f j h]
  exact paste _ _ _ _ _ _ _ _ _ _ h1 hα2 h3

end Stacks.Duality

end
