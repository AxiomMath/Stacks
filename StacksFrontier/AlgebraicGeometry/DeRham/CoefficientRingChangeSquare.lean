module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRingChange
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBaseProjection

/-!
# The square relating the coefficient-ring change to the relative base morphism

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. The space `X` carries the two
inverse-image structure sheaves `f^{-1}𝒪_Y` and `(f ∘ g)^{-1}𝒪_S`, and there are two ways of
getting from `(X, f^{-1}𝒪_Y)` to `(Y, g^{-1}𝒪_S)`: re-read the coefficients over
`(f ∘ g)^{-1}𝒪_S` and then project along `f`, or project along `f` to `(Y, 𝒪_Y)` and then
re-read the coefficients over `g^{-1}𝒪_S`. This file proves that those two morphisms of ringed
spaces agree.

Together with the composition isomorphism for derived direct image this is what turns `R^nf_*`
of a complex read over `(f ∘ g)^{-1}𝒪_S` into `R^nf_*` taken over `f^{-1}𝒪_Y` and then
restricted to `g^{-1}𝒪_S`, which is the shape in which the first page of the spectral sequence
of Section 0FMK is stated.

## Main results

* `Stacks.DeRhamSmooth.coefficientRingChange_relativeBase_c`: the structure-map identity of the
  square, at the level of sheaves of commutative rings on `X`.
* `Stacks.DeRhamSmooth.coefficientRingChange_comp_relativeBase`: **the square of ringed spaces
  commutes.**

## Implementation notes

Both composites have underlying continuous map that of `f` — one as `𝟙 ≫ f.base`, the other as
`f.base ≫ 𝟙`, definitionally but not syntactically equal — so the equality is proved through
`AlgebraicGeometry.PresheafedSpace.hext` rather than the `ext` lemma, as the two triangles of
`StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRingChange` are: the `ext` lemma would insert
an `eqToHom` along the proof of equality of the base maps which nothing then removes.

The structure maps agree because both transpose, along the inverse-image/direct-image adjunction
for `g`, to `g^♯` followed by `g_*` of the unit of `f^{-1} ⊣ f_*`. For the second composite that
is immediate from the definitions of the structure map `g^{-1}𝒪_S ⟶ 𝒪_Y` and of the unit; for
the first it is exactly the defining property of
`Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap`, whose transpose along
`(f ∘ g)^{-1} ⊣ (f ∘ g)_*` is that composite, the direct image along `f ∘ g` being the direct
image along `g` of the direct image along `f` on the nose.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)

universe u

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The structure-map identity of the square**: the comorphism of `relativeBase f g` followed
by the direct image along `f` of the canonical homomorphism `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is
the structure map `g^{-1}𝒪_S ⟶ 𝒪_Y` followed by the unit `𝒪_Y ⟶ f_*f^{-1}𝒪_Y`. Both sides
transpose along `g^{-1} ⊣ g_*` to `g^♯` followed by `g_*` of that unit. -/
theorem coefficientRingChange_relativeBase_c :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv S.sheaf
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))).symm
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ g).base).unit.app
          S.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
        (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) =
    inverseImageStructureMap g ≫
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app Y.sheaf := by
  have hL := (Adjunction.homEquiv_naturality_right_symm
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ g).base).unit.app S.sheaf)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
        (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom))).symm
  have hR := (Adjunction.homEquiv_naturality_right_symm
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base)
      (⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
        Y.sheaf)).symm
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv S.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf))).symm ?_
  refine (Adjunction.homEquiv_unit
    (adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ g).base)
    (f := baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).symm.trans ?_
  exact Equiv.apply_symm_apply _ _

/-- **The square of ringed spaces commutes**: re-reading the coefficients of an
`f^{-1}𝒪_Y`-module over `(f ∘ g)^{-1}𝒪_S` and then projecting to `(Y, g^{-1}𝒪_S)` is projecting
to `(Y, 𝒪_Y)` and then re-reading the coefficients over `g^{-1}𝒪_S`. -/
theorem coefficientRingChange_comp_relativeBase :
    coefficientRingChange f g ≫ relativeBase f g =
      inverseImageBaseProjection f ≫ toInverseImageBase g :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl
    (heq_of_eq (congrArg (fun t => t.hom) (coefficientRingChange_relativeBase_c f g))))

end Stacks.DeRhamSmooth

end
