module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackCompCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula

/-!
# The chart formula for composition with the counit along an étale morphism

Let `pU : X' ⟶ X` be an **étale** morphism of algebraic spaces over a scheme `S` of a big fppf
site `B` and let `f : X ⟶ Y` be arbitrary.
`AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence`
(`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackCompCorrespondence.lean`) asks
for a bijection between linear maps of sections along `f` out of `p_{U*}N` and linear maps of
sections along `p_U ≫ f` out of `N`, whose value at a chart diagram `e` is the counit of the
direct image along `p_U` at the identity-vertical diagram of `e.U`, applied to the value of the
given map at the source-postcomposed diagram of `e`.

This file discharges it.  The bijection is composition with the counit, in the form
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFMapCompChartFormula.lean`, taken at the comparison
of direct images of Stacks 03LU in the transported form of
`AlgebraicGeometry.Space.pushforwardModulesCompAt`; and the chart formula is the chart formula
of that file, which holds on the chart diagrams over `p_U ≫ f` that factor through an étale
chart of `X`.  Every chart diagram over `p_U ≫ f` does factor, `p_U` being étale: the chart of
`X'` postcomposed with `p_U` is an étale chart of `X`, and the factorization is the identity
followed by the vertical morphism of the diagram.  That is the whole of why étaleness of `p_U`
is needed, and it is the reason the formula holds at *every* chart diagram here while the
set-level formula `AlgebraicGeometry.Space.FMap.comp_app` holds only at the factoring ones.

## Main definitions

* `AlgebraicGeometry.Space.moduleFMapCompCounit`: composition with the counit of the direct image
  along `p_U`, relative to a comparison of the direct images.

## Main results

* `AlgebraicGeometry.Space.bijective_moduleFMapCompCounit`: it is a bijection.
* `AlgebraicGeometry.Space.moduleFMapCompCounit_app`: **its chart formula, at every chart diagram
  over `p_U ≫ f`.**
* `AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence`: so
  `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` holds.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`:
  **the canonical base-change comparison at a quasi-coherent module over a diagram of affine
  étale charts is bijective**, with no hypothesis beyond quasi-coherence of the module and
  affineness of the two charts.  This is the chart bijectivity of Stacks 083K, and through
  `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_compCorrespondence` it is
  what the correspondence above is carried for.

## Implementation notes

The comparison of direct images is a parameter throughout, and is instantiated to
`AlgebraicGeometry.Space.pushforwardModulesCompAt` transported along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` only inside the *theorem*
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence`.  Naming that transported
comparison as a definition of its own does not pass the kernel: Lean lifts the three equalities
of functors out of the definition's value into auxiliary theorems, after which an argument's
inferred type is no longer syntactically the parameter type and the structural shortcut is
replaced by a full definitional check which reaches the comparison equivalence of Stacks 03G1
and does not terminate.  Theorems are not subject to that lift, so the instantiation is free
there.

The composite chart diagram of the factorization is
`AlgebraicGeometry.Space.ChartDiagram.comp` of the identity-vertical diagram and the
source-postcomposed diagram, whose vertical morphism is `𝟙 ≫ e.g` and not `e.g`; the two
diagrams are equal by `AlgebraicGeometry.Space.ChartDiagram.ext`, and the components are
transported along that equality by `AlgebraicGeometry.Space.FMap.app_heq`, the components of a
linear map of sections being the components of the `f`-map underlying it.

The two directions of the module chart correspondence are used through
`AlgebraicGeometry.Space.moduleFMapHom_injective` and
`AlgebraicGeometry.Space.moduleFMapHom_modulePushforwardHomFMap` rather than through the
coercion of `AlgebraicGeometry.Space.modulePushforwardHomEquiv`, so that no `Equiv` coercion has
to be unfolded inside a larger term.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The two directions of the module chart correspondence, as plain functions -/

/-- The morphism of modules of a linear map of sections determines it: the two directions of the
module chart correspondence of Stacks 03G4 are mutually inverse. -/
theorem moduleFMapHom_injective (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    Function.Injective (moduleFMapHom B S hS f F G) :=
  Function.LeftInverse.injective (modulePushforwardHomFMap_moduleFMapHom B S hS f F G)

section Source

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom) (N : Modules.{u, u} B S hS X'.1 X'.2)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (ι : modulePushforward B S hS pU ⋙ modulePushforward B S hS f ≅
      modulePushforward B S hS (pU ≫ f))

/-- **Composition with the counit of the direct image along `p_U`**: a linear map of sections
along `f` out of `p_{U*}N` becomes a linear map of sections along `p_U ≫ f` out of `N`, by
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` at the counit of the chartwise universal property
of the direct image along `p_U`. -/
noncomputable def moduleFMapCompCounit
    (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M) :
    ModuleFMap B S hS (pU ≫ f) N M :=
  ModuleFMap.compOfIso B S hS pU f N ((modulePushforward B S hS pU).obj N) M ξ
    (modulePushforwardCounit B S hS pU N) ι

/-- Composition with the counit is, on morphisms of modules, composition with the comparison of
the direct images: the morphism of modules of the counit is the identity. -/
theorem moduleFMapCompHom_modulePushforwardCounit
    (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M) :
    moduleFMapCompHom B S hS pU f N ((modulePushforward B S hS pU).obj N) M ξ
        (modulePushforwardCounit B S hS pU N) ι =
      moduleFMapHom B S hS f ((modulePushforward B S hS pU).obj N) M ξ ≫ ι.hom.app N := by
  rw [moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardCounit,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The morphism of modules of the composite with the counit is the morphism of modules of the
given linear map of sections followed by the comparison of the direct images. -/
theorem moduleFMapHom_moduleFMapCompCounit
    (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M) :
    moduleFMapHom B S hS (pU ≫ f) N M (moduleFMapCompCounit B S hS pU f N M ι ξ) =
      moduleFMapHom B S hS f ((modulePushforward B S hS pU).obj N) M ξ ≫ ι.hom.app N :=
  (moduleFMapHom_modulePushforwardHomFMap B S hS (pU ≫ f) N M
      (moduleFMapCompHom B S hS pU f N ((modulePushforward B S hS pU).obj N) M ξ
        (modulePushforwardCounit B S hS pU N) ι)).trans
    (moduleFMapCompHom_modulePushforwardCounit B S hS pU f N M ι ξ)

/-- **Composition with the counit is a bijection.**  Its effect on morphisms of modules is
composition with an isomorphism, and a linear map of sections is determined by its morphism of
modules. -/
theorem bijective_moduleFMapCompCounit :
    Function.Bijective (moduleFMapCompCounit B S hS pU f N M ι) := by
  have hhom := moduleFMapHom_moduleFMapCompCounit B S hS pU f N M ι
  refine ⟨Function.Injective.of_comp (f := moduleFMapHom B S hS (pU ≫ f) N M) ?_, fun ζ ↦ ?_⟩
  · rw [show moduleFMapHom B S hS (pU ≫ f) N M ∘ moduleFMapCompCounit B S hS pU f N M ι = _ from
      funext hhom]
    exact fun ξ ζ h ↦ moduleFMapHom_injective B S hS f ((modulePushforward B S hS pU).obj N) M
      ((Iso.cancel_iso_hom_right _ _ (ι.app N)).mp h)
  · refine ⟨modulePushforwardHomFMap B S hS f ((modulePushforward B S hS pU).obj N) M
      (moduleFMapHom B S hS (pU ≫ f) N M ζ ≫ ι.inv.app N), ?_⟩
    refine moduleFMapHom_injective B S hS (pU ≫ f) N M ?_
    refine (hhom _).trans ?_
    refine Eq.trans (congrArg (fun a ↦ a ≫ ι.hom.app N)
      (moduleFMapHom_modulePushforwardHomFMap B S hS f
        ((modulePushforward B S hS pU).obj N) M _)) ?_
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-! ### The chart formula -/

variable (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom)

/-- Every chart diagram over `p_U ≫ f` factors through the étale chart of `X` obtained by
postcomposing its own chart of `X'` with `p_U`, by the identity followed by its own vertical
morphism: the composite of the identity-vertical diagram of `e.U` and the source-postcomposed
diagram of `e` is `e` itself. -/
theorem chartDiagram_comp_etaleUnit_postcompSource :
    ChartDiagram.comp B S hS pU f (ChartDiagram.etaleUnit B S hS pU hU e.U).g
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).g
        (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm = e :=
  ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (Category.id_comp e.g))

/-- **The chart formula for composition with the counit.**  At every chart diagram over
`p_U ≫ f`, the composite is the counit of the direct image along `p_U` at the identity-vertical
diagram of `e.U`, applied to the value of the given linear map of sections at the
source-postcomposed diagram of `e`. -/
theorem moduleFMapCompCounit_app
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map (ι.hom.app N) =
      (smallToposMorphismTypeU_comp B S hS pU f).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N))
    (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M)
    (s : M.val.obj (op e.V)) :
    (moduleFMapCompCounit B S hS pU f N M ι ξ).app e s =
      (modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U)
        (ξ.app (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) := by
  refine Eq.trans (eq_of_heq (FMap.app_heq B S hS
    (ModuleFMap.toFMap B S hS (moduleFMapCompCounit B S hS pU f N M ι ξ))
    (chartDiagram_comp_etaleUnit_postcompSource B S hS pU f hU e) (HEq.refl s))).symm ?_
  exact ModuleFMap.compOfIso_app B S hS pU f
    (ChartDiagram.etaleUnit B S hS pU hU e.U).g
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).g
    (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm
    N ((modulePushforward B S hS pU).obj N) M ξ (modulePushforwardCounit B S hS pU N) ι hι s

/-- **The correspondence asked for by
`AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence`, at one pair of modules and
relative to a comparison of the direct images.**  The conclusion does not mention the
comparison, so instantiating it costs nothing. -/
theorem exists_bijective_moduleFMapCompCounit
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map (ι.hom.app N) =
      (smallToposMorphismTypeU_comp B S hS pU f).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)) :
    ∃ Ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M →
        ModuleFMap B S hS (pU ≫ f) N M,
      Function.Bijective Ξ ∧
        ∀ (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M)
          (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)),
          (Ξ ξ).app e s =
            (modulePushforwardCounit B S hS pU N).app
              (ChartDiagram.etaleUnit B S hS pU hU e.U)
              (ξ.app (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) :=
  ⟨moduleFMapCompCounit B S hS pU f N M ι,
    bijective_moduleFMapCompCounit B S hS pU f N M ι,
    fun ξ e s ↦ moduleFMapCompCounit_app B S hS pU f hU N M ι e hι ξ s⟩

end Source

/-- **The chart formula for composition with the counit of a direct image along an étale
morphism holds.**  The bijection is composition with the counit at the comparison
`p_{U*} ∘ f_* ≅ (p_U ≫ f)_*` of Stacks 03LU, whose underlying map of sheaves of sets is the
geometric comparison of Stacks 03G2, part (3), by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`; and its chart
formula is the chart formula of `AlgebraicGeometry.Space.ModuleFMap.compOfIso`, which applies at
every chart diagram over `p_U ≫ f` because `p_U` is étale and every such diagram therefore
factors through an étale chart of `X`. -/
theorem moduleFMapEtaleSourceCompCorrespondence {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X)
    (f : X ⟶ Y) (hU : IsEtale B S hS pU.hom) :
    ModuleFMapEtaleSourceCompCorrespondence B S hS pU f hU :=
  ⟨fun N M ↦ exists_bijective_moduleFMapCompCounit B S hS pU f hU N M
    (modulePushforwardCompIso B S hS pU f)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS pU f N)⟩

/-- **The canonical base-change comparison at a quasi-coherent module over a diagram of affine
étale charts is bijective.**  For a morphism `f : X ⟶ Y` of algebraic spaces, a quasi-coherent
`𝒪_Y`-module `M` and a diagram `d` of affine étale scheme charts over `f`, the sections of
`f^*M` over `d.U` are the base change of the sections of `M` over `d.V` along the pullback of
regular functions, by the canonical comparison
`AlgebraicGeometry.Space.modulePullbackChartBaseChange`.

This is the chart bijectivity of Stacks 083K.  No presentation of `M` is assumed and no
hypothesis beyond quasi-coherence of the module and affineness of the two charts is carried: the
chart formula for composition with the counit along the étale structure morphism of `d.U`, which
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_compCorrespondence` consumes,
is `AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence`. -/
theorem bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f M d) :=
  bijective_modulePullbackChartBaseChange_of_compCorrespondence B S hS f M hM d haU haV
    (moduleFMapEtaleSourceCompCorrespondence B S hS (chartToSpace B S hS X d.U) f
      (isEtale_chartToSpace B S hS X d.U))

end AlgebraicGeometry.Space

end
