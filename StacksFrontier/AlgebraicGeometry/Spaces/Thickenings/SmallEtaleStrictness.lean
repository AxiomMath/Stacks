module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationOfReduction
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# Strictness of the cartesian square of a thickening of algebraic spaces, on sections

Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `Z ⊆ Y` be a closed subspace
and let `g⁻¹(Z) ⊆ X` be its inverse image, so that

```
  g⁻¹(Z) --> X
    |        |
    v        v
    Z  ----> Y
```

is cartesian. On the small étale ringed topoi this square is strict (Stacks 08M9): the defining
ideal of `g⁻¹(Z)` is generated, as an `𝒪_X`-module, by the image of the defining ideal of `Z`
under `g^♯`. This file proves that statement in the form the proof of Stacks 08VU consumes,
`Deformation.ToposThickening.ReductionPresentation.KernelGeneratedByImage`: the generators are
images, under the inverse-image form `g⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map, of sections of
`g⁻¹𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.fSharpInverseImage_inverseImageChartSection`: the section of `g⁻¹𝒪_Y`
  over an étale chart of `X` attached to a regular function on an étale chart of `Y` below it is
  carried by `g⁻¹𝒪_Y ⟶ 𝒪_X` to the pullback of that function.
* `AlgebraicGeometry.Space.kernelGeneratedByImage_preimageSubspace`: the strictness statement.

## How the proof goes

Over a diagram of étale scheme charts `W ⟶ V` over `g` with both charts affine, the defining
ideal of `g⁻¹(Z)` at `W` is the extension of the defining ideal of `Z` at `V`
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map_chartDiagram`), and such charts cover
the small étale site of `X` (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`).
A regular function `s` on `V` gives a section of `g_*g⁻¹𝒪_Y` over `V` through the unit of
`g⁻¹ ⊣ g_*`, and its chart projection to `W` is a section of `g⁻¹𝒪_Y` over `W` which
`g⁻¹𝒪_Y ⟶ 𝒪_X` sends to the pullback of `s`: the two forms of the structure map are adjunct, and
the chart projection of `g^♯(s)` is the pullback of `s`
(`AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet_chartDiagram`).

## References

* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor
  commRingImageAdjunction)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

omit hS in
/-- Forgetting a morphism of sheaves of commutative rings to sheaves of sets factors through
sheaves of rings. -/
theorem sheafCompose_forget_map_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget CommRingCat.{u})] [J.HasSheafCompose (forget RingCat.{u})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {P Q : Sheaf J CommRingCat.{u}} (φ : P ⟶ Q) :
    (sheafCompose J (forget CommRingCat.{u})).map φ =
      (sheafCompose J (forget RingCat.{u})).map
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) :=
  rfl

/-- The structure map of the morphism of small étale ringed topoi, on underlying sheaves of
sets, is `AlgebraicGeometry.Space.structureSharpSet`. -/
theorem forget_map_fSharp_app (g : X ⟶ Y) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj V)) :
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS g).fSharp).hom.app V s =
      (structureSharpSet B S hS g).hom.app V s := by
  refine (congrArg (fun m => m.hom.app V s)
    (sheafCompose_forget_map_eq (smallEtaleRingedToposHom B S hS g).fSharp)).trans ?_
  dsimp only
  rw [forgetCommRingSheaf_map_fSharp]
  rfl

/-- The section of `g⁻¹𝒪_Y` over the chart `d.U` of `X` attached to a regular function on the
chart `d.V` of `Y`: the chart projection of its image under the unit of `g⁻¹ ⊣ g_*`. -/
noncomputable def inverseImageChartSection (g : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 g.hom)
    (s : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    ToType (((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op d.U)) :=
  (directImageChartProjection B S hS g d.V
      (StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS g d).op)).app
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
      ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O))
    (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
      ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).unit.app
        (smallEtaleRingedTopos B S hS Y).O)).hom.app (op d.V) s)

/-- **The section of `g⁻¹𝒪_Y` attached to a regular function is carried to its pullback.** -/
theorem fSharpInverseImage_inverseImageChartSection (g : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 g.hom)
    (s : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    (smallEtaleRingedToposHom B S hS g).fSharpInverseImage.hom.app (op d.U)
        (inverseImageChartSection B S hS g d s) =
      (chartDiagramPullback B S hS g d).hom s := by
  let ρ := (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
  let ε := (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).unit.app
    (smallEtaleRingedTopos B S hS Y).O
  have h1 := directImageChartProjection_map B S hS g d.V
    (StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS g d).op)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ρ)
    (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map ε).hom.app
      (op d.V) s)
  refine h1.symm.trans ?_
  have hadj : ε ≫
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map ρ =
      (smallEtaleRingedToposHom B S hS g).fSharp := by
    have := ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
      _ _).apply_symm_apply (smallEtaleRingedToposHom B S hS g).fSharp
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h2 : ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
      (ε ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map ρ)).hom.app
        (op d.V) s =
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS g).fSharp).hom.app (op d.V) s := by
    rw [hadj]
  rw [CategoryTheory.Functor.map_comp] at h2
  have h3 := forget_map_fSharp_app B S hS g (op d.V) s
  have h4 : (smallEtaleDirectImage B S hS g ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op d.V)).map
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ρ)
        (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map ε).hom.app
          (op d.V) s) = (structureSharpSet B S hS g).hom.app (op d.V) s := by
    refine Eq.trans ?_ (h2.trans h3)
    have h5 := Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS Y.1)
      (Φ := (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward) ρ
    have h6 := congrArg (fun m => m.hom.app (op d.V)
      (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map ε).hom.app
        (op d.V) s)) h5
    exact h6.symm
  rw [h4]
  exact directImageChartProjection_structureSharpSet_chartDiagram B S hS g d s


open Deformation.ToposThickening.ReductionPresentation in
/-- Strictness on one diagram of étale scheme charts with both charts affine: a section of the
defining ideal of `g⁻¹(Z)` over the chart of `X` is a combination of images of sections of
`g⁻¹𝒪_Y` attached to sections of the defining ideal of `Z`. -/
theorem exists_sum_fSharpInverseImage_of_mem_definingIdealAt (g : X ⟶ Y)
    (Z : ClosedSubspaces B S hS Y.1) (d : ChartDiagram B S hS X.1 Y.1 g.hom)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left)]
    (x : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op d.U)))
    (hx : x ∈ definingIdealAt B S hS X (preimageSubspace B S hS g Z) (op d.U)) :
    ∃ (N : ℕ) (b : Fin N → ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op d.U)))
      (y : Fin N → ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))),
        (∀ p, (chartDiagramPullback B S hS g d).hom
          (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj (op d.V)) from y p) ∈
          definingIdealAt B S hS X (preimageSubspace B S hS g Z) (op d.U)) ∧
        x = ∑ p, b p * (chartDiagramPullback B S hS g d).hom
          (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj (op d.V)) from y p) := by
  have hd := definingIdealAt_preimage_eq_map_chartDiagram B S hS g Z d
  rw [hd] at hx ⊢
  obtain ⟨n, c, j, hsum⟩ := Submodule.mem_span_set'.1 hx
  choose y hy hyj using fun i => (j i).2
  refine ⟨n, c, y, fun p => Ideal.mem_map_of_mem _ (hy p), hsum.symm.trans ?_⟩
  exact Finset.sum_congr rfl fun p _ => by rw [← hyj p, smul_eq_mul]; rfl

open Deformation.ToposThickening.ReductionPresentation in
/-- Strictness on one étale chart of `X` lying over an étale chart of `Y`, both affine. -/
theorem exists_sum_ringMapApp_of_mem_definingIdealAt (g : X ⟶ Y)
    (Z : ClosedSubspaces B S hS Y.1) (W : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (q : W.1.left ⟶ V.1.left) (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left)]
    (x : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op W)))
    (hx : x ∈ definingIdealAt B S hS X (preimageSubspace B S hS g Z) (op W)) :
    ∃ (N : ℕ) (b : Fin N → ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS X).O).obj.obj (op W)))
      (α : Fin N → ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
        ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
          (smallEtaleRingedTopos B S hS Y).O)).obj.obj (op W))),
      (∀ p, ringMapApp (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X (preimageSubspace B S hS g Z))).fSharp _
        (ringMapApp (smallEtaleRingedToposHom B S hS g).fSharpInverseImage _ (α p)) = 0) ∧
        x = ∑ p, b p *
          ringMapApp (smallEtaleRingedToposHom B S hS g).fSharpInverseImage _ (α p) := by
  let d : ChartDiagram B S hS X.1 Y.1 g.hom := ⟨W, V, q, hq.symm⟩
  have key := exists_sum_fSharpInverseImage_of_mem_definingIdealAt B S hS g Z d x hx
  rcases key with ⟨N, b, y, hy, hsum⟩
  have hρ : ∀ p, ringMapApp (smallEtaleRingedToposHom B S hS g).fSharpInverseImage (op W)
      (inverseImageChartSection B S hS g d (y p)) = (chartDiagramPullback B S hS g d).hom (y p) :=
    fun p => fSharpInverseImage_inverseImageChartSection B S hS g d (y p)
  have hπ : ∀ p, ringMapApp (smallEtaleRingedToposHom B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z))).fSharp _
        ((chartDiagramPullback B S hS g d).hom (y p)) = 0 := fun p => by
    have h := hy p
    rw [definingIdealAt_eq_ker_fSharp] at h
    exact h
  exact ⟨N, b, fun p => inverseImageChartSection B S hS g d (y p),
    fun p => (congrArg _ (hρ p)).trans (hπ p),
    hsum.trans (Finset.sum_congr rfl fun p _ => congrArg (b p * ·) (hρ p).symm)⟩

open Deformation.ToposThickening.ReductionPresentation in
/-- **Strictness of the cartesian square of a closed subspace, on sections.** For a morphism
`g : X ⟶ Y` and a closed subspace `Z ⊆ Y`, every section of the defining ideal of `g⁻¹(Z)` is
locally an `𝒪_X`-linear combination of images under `g⁻¹𝒪_Y ⟶ 𝒪_X` of sections of `g⁻¹𝒪_Y`
whose images lie in that ideal. -/
theorem kernelGeneratedByImage_preimageSubspace (g : X ⟶ Y) (Z : ClosedSubspaces B S hS Y.1) :
    KernelGeneratedByImage (C := SmallEtale B S hS X.1) (J := SmallEtale.topology B S hS X.1)
      (A := (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O) (O := (smallEtaleRingedTopos B S hS X).O)
      (R := (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS g Z))).toToposHom).obj
          (smallEtaleRingedTopos B S hS ⟨(preimageSubspace B S hS g Z).1.toFunctor,
            (preimageSubspace B S hS g Z).2.1⟩).O)
      (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
      (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS g Z))).fSharp := by
  classical
  apply kernelGeneratedByImage_of_presieve
  intro U x hx
  have hxI : x ∈ definingIdealAt B S hS X (preimageSubspace B S hS g Z) (op U) := by
    rw [definingIdealAt_eq_ker_fSharp]
    exact hx
  refine ⟨fun W _ => HasAffineChartDiagram B S hS g W,
    mem_topology_of_hasAffineChartDiagram B S hS g U _ fun W a ha => Sieve.le_generate _ W a ha,
    ?_⟩
  rintro W a ⟨hWaff, V, q, hq, hVaff⟩
  have := hWaff
  have := hVaff
  exact exists_sum_ringMapApp_of_mem_definingIdealAt B S hS g Z W V q hq _
    (definingIdealAt_map B S hS X (preimageSubspace B S hS g Z) a.op x hxI)

end AlgebraicGeometry.Space

end
