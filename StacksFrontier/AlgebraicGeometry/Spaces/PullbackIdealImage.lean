module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackUnitGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem

/-!
# The inverse-image ideal of an arbitrary morphism of algebraic spaces

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `𝓘 ⊆ 𝒪_{X'}` be a sheaf of ideals on the small étale site of `X'`.  The
inclusion `𝓘 ⊆ 𝒪_{X'}` has an inverse image `g^*𝓘 ⟶ g^*𝒪_{X'} ⟶ 𝒪_X`, the second map being
the canonical `AlgebraicGeometry.Space.structureModulePullbackMap` of Stacks 03G8, and the image
of that composite is the ideal `g⁻¹𝓘 · 𝒪_X`.  **This file constructs that ideal for an arbitrary
morphism of algebraic spaces and identifies the sections that visibly lie in it: over a
commutative diagram `d` of étale scheme charts, the pullback along the vertical morphism of `d`
of a section of `𝓘 ⁿ` is a section of `(g⁻¹𝓘 · 𝒪_X) ⁿ`.**

`AlgebraicGeometry.Space.pullbackIdealSubsheaf` is the same ideal described differently — as the
smallest sheaf of ideals containing the pullbacks `g♯(a)` of the sections of `𝓘` over the
*base-changed* charts `Q ×_{X'} X` — and that description is available only for a *representable*
`g`, since the base change of a chart of `X'` along `g` need not be a scheme otherwise.  The
image description below carries no such hypothesis, which is what makes it the inverse-image
ideal of the arbitrary morphism of Noetherian algebraic spaces of Stacks 089P (3).

## Main definitions

* `AlgebraicGeometry.Space.pullbackIdealHom` — the morphism `g^*𝓘 ⟶ 𝒪_X` of `𝒪_X`-modules
  induced by the inclusion `𝓘 ⊆ 𝒪_{X'}`.
* `AlgebraicGeometry.Space.pullbackIdealImage` — **the inverse-image ideal `g⁻¹𝓘 · 𝒪_X`**, the
  image subsheaf of that morphism.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_pullbackIdealHom_app` — the chartwise transpose
  of `g^*𝓘 ⟶ 𝒪_X` is pullback of regular functions along the vertical morphism of a chart
  diagram.
* `AlgebraicGeometry.Space.pullbackIdealHom_unitSection` — the value of `g^*𝓘 ⟶ 𝒪_X` on the unit
  section of a section `a` of `𝓘` is the pullback of `a`.
* `AlgebraicGeometry.Space.chartDiagramPullback_mem_chartIdeal_pullbackIdealImage` — **the
  pullback of a section of `𝓘` along the vertical morphism of a chart diagram is a section of
  `g⁻¹𝓘 · 𝒪_X`.**
* `AlgebraicGeometry.Space.chartDiagramPullback_pow_mem_chartIdeal_pullbackIdealImage` — the same
  for the `n`-th powers: the pullback of a section of `𝓘 ⁿ` is a section of `(g⁻¹𝓘 · 𝒪_X) ⁿ`,
  pullback of regular functions being a ring homomorphism.

## Implementation notes

The image is `Stacks.SheafOfModules.localImage`, the sheaf of sections lying locally in the
pointwise image, because the pointwise image of a morphism of sheaves of modules is only a
presheaf submodule.  That is the same construction `Stacks.SheafOfModules.localSpan` is built
from, so the membership statements here and the local generation statement of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackUnitGeneration` are about one object.

The chartwise transpose of `g^*𝓘 ⟶ 𝒪_X` is computed from the two naturality statements of the
chart correspondence rather than by unfolding it:
`CategoryTheory.Adjunction.homEquiv_naturality_left` moves the inverse image of `𝓘 ⊆ 𝒪_{X'}`
across the Stacks 03D7 transpose and
`AlgebraicGeometry.Space.modulePushforwardHomEquiv_app_comp_left` moves it across the Stacks 03LU
transpose; what is left is the transpose of
`AlgebraicGeometry.Space.structureModulePullbackMap`, which is
`AlgebraicGeometry.Space.structureModuleFMap` by its characterising property.

Pullback of regular functions is written as the value of
`AlgebraicGeometry.Space.structureModuleFMap` wherever the argument is a section of the submodule
`𝓘` rather than of `𝒪_{X'}`.  At the spelling `chartDiagramPullback … (𝓘.ι.val.app …)` the
elaborator would have to identify the sections of the unit module with the sections of the sheaf
of rings underneath a `CategoryTheory.ConcreteCategory` coercion; `structureModuleFMap` takes its
argument at the module spelling and the problem does not arise.  Where the argument is already a
section of `𝒪_{X'}`, as in the two membership statements, `chartDiagramPullback` is used
directly.

What is *not* proved here is the converse description, that every section of `g⁻¹𝓘 · 𝒪_X` is
locally a combination of such pullbacks.  It is true, and its two halves are available —
`AlgebraicGeometry.Space.spanSieve_modulePullbackUnitSections_mem` writes a section of `g^*𝓘`
locally as a combination of unit sections, and a section of the image lies locally in the
pointwise image — but composing them means refining one covering along another, and nothing below
needs it.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the canonical morphism
  of small étale ringed topoi and its structure map.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0GF8](https://stacks.math.columbia.edu/tag/0GF8), the inverse-image ideal
  acting on modules.
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)

/-! ### The inverse image of the inclusion of a sheaf of ideals -/

/-- The morphism `g^*𝓘 ⟶ 𝒪_X` induced by the inclusion `𝓘 ⊆ 𝒪_{X'}`: the inverse image of that
inclusion, followed by the canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` of Stacks 03G8. -/
def pullbackIdealHom :
    (modulePullback B S hS g).obj 𝓘.toSheafOfModules ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  (modulePullback B S hS g).map 𝓘.ι ≫ structureModulePullbackMap B S hS g

/-- **The chartwise transpose of `g^*𝓘 ⟶ 𝒪_X` is pullback of regular functions.**  On a
commutative diagram `d` of étale scheme charts it sends a section `a` of `𝓘` over the chart of
`X'` to the pullback of `a` along the vertical morphism of `d`. -/
theorem modulePullbackHomFMap_pullbackIdealHom_app
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (a : 𝓘.toSheafOfModules.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS g 𝓘.toSheafOfModules _ (pullbackIdealHom B S hS g 𝓘)).app d a =
      (structureModuleFMap B S hS g).app d (𝓘.ι.val.app (op d.V) a) :=
  have hnat : (modulePullbackAdjunction B S hS g).homEquiv 𝓘.toSheafOfModules _
      (pullbackIdealHom B S hS g 𝓘) =
      𝓘.ι ≫ (modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g) :=
    (modulePullbackAdjunction B S hS g).homEquiv_naturality_left 𝓘.ι
      (structureModulePullbackMap B S hS g)
  have htr : modulePushforwardHomEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X'))
      ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g)) =
      structureModuleFMap B S hS g :=
    (congrArg (modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X')))
      (structureModulePullbackMap_transpose B S hS g)).trans
      ((modulePushforwardHomEquiv B S hS g _ _).apply_symm_apply _)
  ((congrArg (fun φ : 𝓘.toSheafOfModules ⟶
        (modulePushforward B S hS g).obj (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) =>
      (modulePushforwardHomEquiv B S hS g _ _ φ).app d a) hnat).trans
    ((modulePushforwardHomEquiv_app_comp_left B S hS g 𝓘.ι
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g)) d a).trans
      (congrArg (fun ξ : ModuleFMap B S hS g
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (SheafOfModules.unit (structureRingSheaf B S hS X')) =>
          ξ.app d (𝓘.ι.val.app (op d.V) a)) htr)))

/-- **The morphism `g^*𝓘 ⟶ 𝒪_X` carries a unit section to a pullback of regular functions.**
This is `AlgebraicGeometry.Space.modulePullbackHomFMap_app` read through the computation of the
chartwise transpose. -/
theorem pullbackIdealHom_unitSection (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (a : 𝓘.toSheafOfModules.val.obj (op d.V)) :
    (pullbackIdealHom B S hS g 𝓘).val.app (op d.U)
        (modulePullbackUnitSection B S hS g 𝓘.toSheafOfModules d a) =
      (structureModuleFMap B S hS g).app d (𝓘.ι.val.app (op d.V) a) :=
  (modulePullbackHomFMap_app B S hS g 𝓘.toSheafOfModules _
    (pullbackIdealHom B S hS g 𝓘) d a).symm.trans
    (modulePullbackHomFMap_pullbackIdealHom_app B S hS g 𝓘 d a)

/-! ### The inverse-image ideal -/

/-- **The inverse-image ideal `g⁻¹𝓘 · 𝒪_X`** of a sheaf of ideals `𝓘 ⊆ 𝒪_{X'}` along an
arbitrary morphism `g : X ⟶ X'` of algebraic spaces: the image of the morphism `g^*𝓘 ⟶ 𝒪_X`
induced by the inclusion `𝓘 ⊆ 𝒪_{X'}`. -/
def pullbackIdealImage :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule :=
  Stacks.SheafOfModules.localImage (pullbackIdealHom B S hS g 𝓘).val

/-- **The pullback of a section of `𝓘` along the vertical morphism of a chart diagram is a
section of the inverse-image ideal.**  It is the value of `g^*𝓘 ⟶ 𝒪_X` on the unit section of
that section, so it lies in the pointwise image already and the sieve of local membership in the
image is the maximal sieve. -/
theorem chartDiagramPullback_mem_chartIdeal_pullbackIdealImage
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    {r : chartRing B S hS X'.1 X'.2 d.V} (hr : r ∈ chartIdeal B S hS X' 𝓘 d.V) :
    chartDiagramPullback B S hS g d r ∈
      chartIdeal B S hS X (pullbackIdealImage B S hS g 𝓘) d.U := by
  have hval : (pullbackIdealHom B S hS g 𝓘).val.app (op d.U)
      (modulePullbackUnitSection B S hS g 𝓘.toSheafOfModules d ⟨r, hr⟩) =
      chartDiagramPullback B S hS g d r :=
    pullbackIdealHom_unitSection B S hS g 𝓘 d ⟨r, hr⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((SmallEtale.topology B S hS X.1).top_mem d.U)
  intro V i _
  refine ⟨((modulePullback B S hS g).obj 𝓘.toSheafOfModules).val.map i.op
    (modulePullbackUnitSection B S hS g 𝓘.toSheafOfModules d ⟨r, hr⟩), ?_⟩
  refine (PresheafOfModules.naturality_apply (pullbackIdealHom B S hS g 𝓘).val i.op _).trans ?_
  exact congrArg (fun z => (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))).val.map i.op z) hval

/-- **The pullback of a section of `𝓘 ⁿ` along the vertical morphism of a chart diagram is a
section of the `n`-th power of the inverse-image ideal.**  Pullback of regular functions is a
ring homomorphism, so it carries the `n`-th power of an ideal into the `n`-th power of any ideal
containing the image of that ideal. -/
theorem chartDiagramPullback_pow_mem_chartIdeal_pullbackIdealImage (n : ℕ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    {r : chartRing B S hS X'.1 X'.2 d.V} (hr : r ∈ chartIdeal B S hS X' 𝓘 d.V ^ n) :
    chartDiagramPullback B S hS g d r ∈
      chartIdeal B S hS X (pullbackIdealImage B S hS g 𝓘) d.U ^ n := by
  have hle : Ideal.map (chartDiagramPullback B S hS g d).hom
      (chartIdeal B S hS X' 𝓘 d.V) ≤
      chartIdeal B S hS X (pullbackIdealImage B S hS g 𝓘) d.U := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun _ hx => chartDiagramPullback_mem_chartIdeal_pullbackIdealImage B S hS g 𝓘 d hx
  refine pow_le_pow_left' hle n ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hr

end AlgebraicGeometry.Space

end
