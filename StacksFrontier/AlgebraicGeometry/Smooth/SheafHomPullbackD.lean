module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact

/-!
# Restricting a coefficient of the internal hom to a smaller open

A section of the internal hom sheaf `SheafHom(F, G)` over an open `U` is a morphism
`F|_U ⟶ G|_U`, hence has a component `Γ(F, W) ⟶ Γ(G, W)` over every open `W ≤ U`, and these
components are compatible with restriction of sections. Applied to `F = a^*Ω_{X/S}` and the
pullback of the universal differential, this restricts a coefficient of the internal hom to a
smaller open with no finiteness hypothesis on `f : X ⟶ S`, unlike the restriction
`Stacks.Smooth.homCompare_restrictₗ` of a linear map on sections used in the proof of
[Stacks Project, Tag 02H6], which needs `AlgebraicGeometry.LocallyOfFinitePresentation f`.

## Main definitions

* `Stacks.Smooth.sheafHomApp` is the component over `W ≤ U` of a section of `SheafHom(F, G)`
  over `U`, as a map `Γ(F, W) ⟶ Γ(G, W)`.

## Main results

* `Stacks.Smooth.sheafHomApp_naturality`: the components of one section commute with restriction
  of sections.
* `Stacks.Smooth.sheafHomApp_restrict`: the component over `W` of a section restricted from `U`
  to `V` is the component over `W` of the section itself.
* `Stacks.Smooth.sheafHomApp_pullbackD_restrict`: the two together, applied to the pullback
  `Stacks.Smooth.pullbackD` of the universal differential. The coefficient attached to the
  restricted section, evaluated on the differential formed over the smaller open, is the
  restriction of the value formed over the larger one.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Smooth

section General

variable {Z : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} Z}
  {F G : SheafOfModules.{u} (structureSheaf Rc)} (H : SheafHom Rc F G)

/-- **The component of a section of the internal hom over a smaller open.** A section `θ` of
`SheafHom(F, G)` over `U` is a morphism `F|_U ⟶ G|_U`, and this is its component over `W ≤ U`,
a map from the sections of `F` over `W` to those of `G` over `W`. -/
noncomputable def sheafHomApp {W U : Opens Z} (hWU : W ≤ U) (θ : H.obj.val.obj (op U)) :
    F.val.obj (op W) → G.val.obj (op W) :=
  fun x => (H.sectionsEquiv U θ).val.app (op (Over.mk (homOfLE hWU))) x

/-- **The components of one section commute with restriction of sections.** -/
theorem sheafHomApp_naturality {W W' U : Opens Z} (hWU : W ≤ U) (hW'U : W' ≤ U) (hW'W : W' ≤ W)
    (θ : H.obj.val.obj (op U)) (x : F.val.obj (op W)) :
    sheafHomApp H hW'U θ ((F.val.map (homOfLE hW'W).op) x) =
      (G.val.map (homOfLE hW'W).op) (sheafHomApp H hWU θ x) :=
  PresheafOfModules.naturality_apply (H.sectionsEquiv U θ).val
    (Over.homMk (homOfLE hW'W) : Over.mk (homOfLE hW'U) ⟶ Over.mk (homOfLE hWU)).op x

/-- **Restricting a section does not change its components.** The component over `W` of the
section obtained by restricting `θ` from `U` to `V` is the component of `θ` itself. -/
theorem sheafHomApp_restrict {W V U : Opens Z} (hVU : V ≤ U) (hWV : W ≤ V)
    (θ : H.obj.val.obj (op U)) (x : F.val.obj (op W)) :
    sheafHomApp H hWV (H.obj.val.map (homOfLE hVU).op θ) x =
      sheafHomApp H (hWV.trans hVU) θ x :=
  (H.restrict_natural hVU θ hWV x).symm

end General

section PullbackD

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {G : T.Modules}
  (H : SheafHom T.sheaf (pullbackCotangentSheaf f a) G) (W : X.Opens) {U U' : T.Opens}

/-- **A coefficient of the internal hom restricts to a smaller open, with no finiteness
hypothesis.** Let `H` present the internal hom from `a^*Ω_{X/S}` to a sheaf of modules `G` on
`T`, let `θ` be a section of it over `U` and let `U' ≤ U`. Then the component over `U'` of the
restriction of `θ`, evaluated on the differential `Stacks.Smooth.pullbackD` of a section of
`𝒪_X` over a chart `W` formed over `U'`, is the restriction to `U'` of the component over `U`
evaluated on the differential formed over `U`. Here `f` is arbitrary (compare
`Stacks.Smooth.homCompare_restrictₗ` in the proof of [Stacks Project, Tag 02H6]). -/
theorem sheafHomApp_pullbackD_restrict (hUW : U ≤ a ⁻¹ᵁ W) (hU'W : U' ≤ a ⁻¹ᵁ W)
    (hU'U : U' ≤ U) (θ : H.obj.val.obj (op U)) (b : Γ(X, W)) :
    sheafHomApp H (le_refl U') (H.obj.val.map (homOfLE hU'U).op θ) (pullbackD f a W hU'W b) =
      (G.val.map (homOfLE hU'U).op) (sheafHomApp H (le_refl U) θ (pullbackD f a W hUW b)) := by
  rw [sheafHomApp_restrict H hU'U (le_refl U') θ (pullbackD f a W hU'W b),
    ← map_pullbackD f a W hUW hU'W hU'U b]
  exact sheafHomApp_naturality H (le_refl U) hU'U hU'U θ (pullbackD f a W hUW b)

end PullbackD

end Stacks.Smooth

end
