module

public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtension
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Morphisms of square-zero thickenings compatible with a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, let
`ℱ` be an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module and `c : ℱ ⟶ g_*𝒢` a `g`-map, and let

* `0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` be an extension of `f⁻¹𝒪_S`-algebras, and
* `0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of `(g ∘ f)⁻¹𝒪_S`-algebras,

each with its ideal of square zero, as in **Stacks 0GQ1**. The thickenings `X'` and `Y'` have the
underlying spaces of `X` and `Y`, so an `S`-morphism `g' : Y' ⟶ X'` lying over `g` is its
comorphism `𝒪_{X'} ⟶ g_*𝒪_{Y'}`, a morphism of sheaves of rings on `X`. It is *compatible with
`g`* when it reduces to `g^♯ : 𝒪_X ⟶ g_*𝒪_Y`, it is a morphism over `S` when it is compatible with
the two structure maps `𝒪_S ⟶ f_*𝒪_{X'}` and `𝒪_S ⟶ f_*g_*𝒪_{Y'} = (g ∘ f)_*𝒪_{Y'}`, and it is
*compatible with `c`* when on the ideals it is `c : ℱ ⟶ g_*𝒢`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.CompatibleMorphism`: an `S`-morphism `Y' ⟶ X'`
  compatible with `g` and `c`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} {g : Y ⟶ X}
  {F : SheafOfModules.{u} (structureSheafRing X)} {G : SheafOfModules.{u} (structureSheafRing Y)}

/-- **An `S`-morphism `g' : Y' ⟶ X'` compatible with `g` and the `g`-map `c : ℱ ⟶ g_*𝒢`**, given
by its comorphism `𝒪_{X'} ⟶ g_*𝒪_{Y'}` (the thickenings have the spaces of `X` and `Y`):
it reduces to `g^♯ : 𝒪_X ⟶ g_*𝒪_Y`, it is compatible with the structure maps from `𝒪_S`, and it
restricts to `c` on the ideals `ℱ ⊆ 𝒪_{X'}` and `𝒢 ⊆ 𝒪_{Y'}`. -/
structure CompatibleMorphism (P : SquareZeroAlgebraExtension f F)
    (Q : SquareZeroAlgebraExtension (g ≫ f) G) (c : F ⟶ (modulePushforward g).obj G) where
  /-- The comorphism `𝒪_{X'} ⟶ g_*𝒪_{Y'}` of `g'`. -/
  hom : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Q.sheaf
  /-- `g'` lies over `g`: its reduction is `g^♯`. -/
  reduction_comm : hom ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.reduction =
    P.reduction ≫ (ObjectProperty.homMk g.hom.c : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Y.sheaf)
  /-- `g'` is a morphism over `S`: the structure maps `𝒪_S ⟶ f_*𝒪_{X'} ⟶ f_*g_*𝒪_{Y'}` and
  `𝒪_S ⟶ (g ∘ f)_*𝒪_{Y'}` agree. -/
  base_comm :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _ P.base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map hom =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).homEquiv _ _
        Q.base
  /-- `g'` restricts to `c` on the ideals: for a local section `s` of `ℱ ⊆ 𝒪_{X'}` over `U`, the
  image of `s` in `𝒪_{Y'}(g⁻¹U)` is `c(s) ∈ 𝒢(g⁻¹U) ⊆ 𝒪_{Y'}(g⁻¹U)`. -/
  ideal_comm (U : Opens X.carrier) (s : F.val.obj (op U)) :
    (hom.hom.app (op U)).hom (P.incl (op U) s) =
      Q.incl (op ((Opens.map g.hom.base).obj U)) (c.val.app (op U) s)

end AlgebraicGeometry.RingedSpaceThickening
