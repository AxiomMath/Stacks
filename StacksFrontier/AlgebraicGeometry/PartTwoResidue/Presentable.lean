module

public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralLimitFromAlgebraColimit
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FilteredLimit

/-!
# A finitely presented quasi-coherent algebra is presentable along colimits of quasi-coherent ones

Let `S` be a quasi-compact and quasi-separated scheme and let `B` be a quasi-coherent sheaf of
commutative `𝒪_S`-algebras of finite presentation.  Let `A` be a quasi-coherent algebra sheaf
written as the colimit of a directed system `F` of quasi-coherent algebra sheaves.  Then every
morphism `B ⟶ A` factors through some `F i`, and two morphisms `B ⟶ F i` that agree in `A` are
equalized by a transition of the system.

That is `Stacks.FinitelyPresentableComposition.PresentableAlong B (Cocone.mk A t)`, the hypothesis
the two-stage composition consumes, and it is the last input part (2) of [Stacks, Tag 0817]
needs: what is absent is the *unrestricted* [Stacks, Tag 01BS] for algebra sheaves,
`CategoryTheory.IsFinitelyPresentable` in `Stacks.RelativeSpec.AlgebraSheaf S`, which quantifies
over filtered colimits of algebra sheaves that need not be quasi-coherent.  Along a colimit whose
stages and vertex are quasi-coherent the statement is instead a theorem about schemes, and it is
proved here.

## Route

The relative spectrum is an anti-equivalence between the quasi-coherent algebra sheaves on `S` and
the schemes affine over `S` ([Stacks, Tag 01SA]), so

* `A` is `(relativeSpecToBase A)_* 𝒪` — essential surjectivity, [Stacks, Tag 01LX](3);
* the colimit presentation `t` of `A` becomes a limit cone in `CategoryTheory.Over S` with vertex
  the relative spectrum of `A`, over the inverse system `Stacks.RelativeSpec.affineDiagram` of the
  relative spectra of the `F i` — `Stacks.RelativeSpec.exists_isLimit_leftOp_of_isColimit`, whose
  third conclusion says the legs of that cone are exactly the legs of `t` read through the
  anti-equivalence;
* every stage of the inverse system is affine over `S`, hence quasi-compact and quasi-separated
  because `S` is, and every transition morphism is affine;
* `B` is `(relativeSpecToBase B)_* 𝒪`, and its finite presentation as an algebra makes that
  structure morphism locally of finite presentation
  (`Stacks.IntegralLimit.locallyOfFinitePresentation_of_isFinitePresentation`).

So [Stacks, Tag 01ZC] applies, in the form
`AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions`:
the functor of points of the relative spectrum of `B` turns that limit into a filtered colimit of
sets.  Surjectivity of the comparison is the factorisation, injectivity together with
`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'` is the equalization, and both are
carried back to algebra sheaves by
`Stacks.RelativeSpec.bijective_map_pushforwardAlgebraFunctor`.

## Main results

* `exists_comp_eq_of_isLimitPreservingOnAffineTransitions`: the factorisation a limit-preserving
  functor of points gives, for inverse systems with affine transition morphisms.  This is
  `AlgebraicGeometry.Scheme.exists_comp_eq_of_isLimitPreserving` for the other of the two
  predicates of that file.
* `presentableAlong_of_isFinitePresentation`: **the statement above** — a quasi-coherent algebra
  sheaf of finite presentation on a quasi-compact quasi-separated scheme is finitely presentable
  along every directed colimit of quasi-coherent algebra sheaves.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached here.**  This is not [Stacks, Tag 01BS]: that tag is about
`Hom(𝒢, -)` for a sheaf of *modules* of finite presentation on a ringed space, and is formalized as
`Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`.  Nor is it
tag 01BS transposed to algebras, which would be
`CategoryTheory.IsFinitelyPresentable` in `Stacks.RelativeSpec.AlgebraSheaf S` and is still absent:
the quasi-coherence of the stages and of the vertex is used twice over, to make the relative
spectrum available at all and to make the stages quasi-compact and quasi-separated.  It is
[Stacks, Tag 01ZC] transported along [Stacks, Tag 01SA], and both of those are carried elsewhere.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.AlgebraicGeometry.Tag0817Presentable

/-- A morphism to `X` out of the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes over `S` with affine transition morphisms factors through some member of
the system, as soon as the functor of points of `X` preserves such limits: a filtered colimit of
sets is the union of the images of its legs.

This is `AlgebraicGeometry.Scheme.exists_comp_eq_of_isLimitPreserving` for
`AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions` in place of
`AlgebraicGeometry.Scheme.IsLimitPreserving`. -/
theorem exists_comp_eq_of_isLimitPreservingOnAffineTransitions {S : Scheme.{u}} {X : Over S}
    (H : _root_.AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions S (yoneda.obj X))
    {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ Over S)
    (haff : ∀ (i j : J) (g : i ⟶ j), IsAffineHom (D.map g).left)
    (hqc : ∀ i, CompactSpace (D.obj i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (D.obj i).left)
    (c : Cone D) (hc : IsLimit c) (g : c.pt ⟶ X) :
    ∃ (i : J) (gᵢ : D.obj i ⟶ X), c.π.app i ≫ gᵢ = g := by
  obtain ⟨hcol⟩ := (H J D haff hqc hqs).preserves hc.op
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol g
  exact ⟨j.unop, y, hy⟩

/-- Two morphisms out of one member of a cofiltered inverse system of quasi-compact and
quasi-separated schemes over `S` with affine transition morphisms that agree on the limit are
equalized by a transition morphism, as soon as the functor of points of the target preserves such
limits: this is the injectivity half of the same comparison, through
`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`. -/
theorem exists_map_comp_eq_of_isLimitPreservingOnAffineTransitions {S : Scheme.{u}} {X : Over S}
    (H : _root_.AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions S (yoneda.obj X))
    {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ Over S)
    (haff : ∀ (i j : J) (g : i ⟶ j), IsAffineHom (D.map g).left)
    (hqc : ∀ i, CompactSpace (D.obj i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (D.obj i).left)
    (c : Cone D) (hc : IsLimit c) (j : J) (g₁ g₂ : D.obj j ⟶ X)
    (hg : c.π.app j ≫ g₁ = c.π.app j ≫ g₂) :
    ∃ (k : J) (w : k ⟶ j), D.map w ≫ g₁ = D.map w ≫ g₂ := by
  obtain ⟨hcol⟩ := (H J D haff hqc hqs).preserves hc.op
  obtain ⟨k, w, hw⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol g₁ g₂).mp hg
  exact ⟨k.unop, w.unop, hw⟩

section

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {F : I ⥤ AlgebraSheaf S} (hFqc : ∀ i, (F.obj i).IsQuasicoherent)

/-- Every stage of the inverse system of relative spectra is a quasi-compact space, the base
being quasi-compact and the structure morphism affine. -/
theorem compactSpace_affineDiagram_leftOp (i : Iᵒᵖ) :
    CompactSpace ((affineDiagram F hFqc).leftOp.obj i).left := by
  have : IsAffineHom ((affineDiagram F hFqc).leftOp.obj i).hom :=
    isAffineHom_affineDiagram_leftOp F hFqc i
  rw [← quasiCompact_iff_compactSpace ((affineDiagram F hFqc).leftOp.obj i).hom]
  infer_instance

/-- Every stage of the inverse system of relative spectra is a quasi-separated space, the base
being quasi-separated and the structure morphism affine, hence separated. -/
theorem quasiSeparatedSpace_affineDiagram_leftOp (i : Iᵒᵖ) :
    QuasiSeparatedSpace ((affineDiagram F hFqc).leftOp.obj i).left := by
  have : IsAffineHom ((affineDiagram F hFqc).leftOp.obj i).hom :=
    isAffineHom_affineDiagram_leftOp F hFqc i
  have : IsSeparated ((affineDiagram F hFqc).leftOp.obj i).hom := IsSeparated.of_isAffineHom _
  exact quasiSeparatedSpace_of_quasiSeparated ((affineDiagram F hFqc).leftOp.obj i).hom

/-- Every transition morphism of the inverse system of relative spectra is affine: both its source
and its target are affine over the base, and it commutes with the structure morphisms. -/
theorem isAffineHom_affineDiagram_leftOp_map (i j : Iᵒᵖ) (g : i ⟶ j) :
    IsAffineHom (((affineDiagram F hFqc).leftOp.map g).left) := by
  have : IsAffineHom ((affineDiagram F hFqc).leftOp.obj j).hom :=
    isAffineHom_affineDiagram_leftOp F hFqc j
  have hw : ((affineDiagram F hFqc).leftOp.map g).left ≫
      ((affineDiagram F hFqc).leftOp.obj j).hom = ((affineDiagram F hFqc).leftOp.obj i).hom :=
    Over.w _
  have h1 : IsAffineHom (((affineDiagram F hFqc).leftOp.map g).left ≫
      ((affineDiagram F hFqc).leftOp.obj j).hom) := by
    rw [hw]
    exact isAffineHom_affineDiagram_leftOp F hFqc i
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _
    ((affineDiagram F hFqc).leftOp.obj j).hom (IsSeparated.of_isAffineHom _) h1

include hFqc in
/-- **A quasi-coherent sheaf of commutative `𝒪_S`-algebras of finite presentation is finitely
presentable along every directed colimit of quasi-coherent algebra sheaves**, on a quasi-compact
and quasi-separated scheme `S`.

Concretely: if `A = colim F` with every `F i` quasi-coherent and `A` quasi-coherent, then every
morphism `B ⟶ A` factors through some `F i`, and two morphisms `B ⟶ F i` agreeing in `A` are
equalized by a transition of the system.

This is [Stacks, Tag 01ZC] carried across the anti-equivalence of [Stacks, Tag 01SA]: both sides
of the colimit are relative spectra, the colimit becomes a limit of schemes affine over `S` whose
stages are quasi-compact and quasi-separated and whose transition morphisms are affine, and `B`'s
finite presentation makes its relative spectrum locally of finite presentation over `S`. -/
theorem presentableAlong_of_isFinitePresentation {A : AlgebraSheaf S} (hAqc : A.IsQuasicoherent)
    (t : F ⟶ (Functor.const I).obj A) (ht : IsColimit (Cocone.mk A t))
    {B : AlgebraSheaf S} (hBqc : B.IsQuasicoherent) (hBfp : B.IsFinitePresentation) :
    Stacks.FinitelyPresentableComposition.PresentableAlong B (Cocone.mk A t) := by
  classical
  have : AlgebraSheaf.IsQuasicoherent A := hAqc
  have : AlgebraSheaf.IsQuasicoherent B := hBqc
  let L : Over S := Over.mk (relativeSpecToBase A)
  let W : Over S := Over.mk (relativeSpecToBase B)
  have : IsAffineHom L.hom := isAffineHom_relativeSpecToBase A
  have : IsAffineHom W.hom := isAffineHom_relativeSpecToBase B
  let eA : (pushforwardAlgebraFunctor S).obj (op L) ≅ A := pushforwardAlgebraIso A
  let eB : (pushforwardAlgebraFunctor S).obj (op W) ≅ B := pushforwardAlgebraIso B
  have : LocallyOfFinitePresentation W.hom :=
    Stacks.IntegralLimit.locallyOfFinitePresentation_of_isFinitePresentation
      (relativeSpecToBase B) (AlgebraSheaf.isFinitePresentation_of_iso eB.symm hBfp)
  -- the colimit presentation of `A`, read through the relative spectrum
  let t' : F ⟶ (Functor.const I).obj ((pushforwardAlgebraFunctor S).obj (op L)) :=
    t ≫ (Functor.const I).map eA.inv
  have ht' : IsColimit (Cocone.mk ((pushforwardAlgebraFunctor S).obj (op L)) t') :=
    ht.ofIsoColimit (Cocones.ext eA.symm fun _ => rfl)
  obtain ⟨π, ⟨hπ⟩, hcompat⟩ := exists_isLimit_leftOp_of_isColimit (pushforwardAlgebraFunctor S)
    (affineDiagram F hFqc) L (affineDiagramIso F hFqc) t' ht'
    (fun Q j => bijective_map_pushforwardAlgebraFunctor Q ((affineDiagram F hFqc).obj j).unop)
    (fun Q => bijective_map_pushforwardAlgebraFunctor Q L)
  have H : _root_.AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions S
      (yoneda.obj W) :=
    (Scheme.locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions W.hom).mp
      inferInstance
  have hbij : ∀ Q : Over S, Function.Bijective
      fun h : Q ⟶ W ↦ (pushforwardAlgebraFunctor S).map h.op :=
    fun Q => bijective_map_pushforwardAlgebraFunctor Q W
  refine ⟨fun f => ?_, fun i g₁ g₂ hg => ?_⟩
  · -- the factorisation
    obtain ⟨φ, hφ⟩ : ∃ φ : L ⟶ W,
        (pushforwardAlgebraFunctor S).map φ.op = eB.hom ≫ f ≫ eA.inv :=
      (hbij L).2 _
    obtain ⟨j, ψ, hψ⟩ := exists_comp_eq_of_isLimitPreservingOnAffineTransitions H
      ((affineDiagram F hFqc).leftOp) (isAffineHom_affineDiagram_leftOp_map hFqc)
      (compactSpace_affineDiagram_leftOp hFqc) (quasiSeparatedSpace_affineDiagram_leftOp hFqc)
      (Cone.mk L π) hπ φ
    have key : eB.hom ≫ f ≫ eA.inv = ((pushforwardAlgebraFunctor S).map ψ.op ≫
        (affineDiagramIso F hFqc).hom.app j.unop) ≫ t.app j.unop ≫ eA.inv := by
      rw [← hφ, ← hψ, op_comp, (pushforwardAlgebraFunctor S).map_comp, hcompat j.unop]
      simp only [Category.assoc]
      rfl
    refine ⟨j.unop, eB.inv ≫ (pushforwardAlgebraFunctor S).map ψ.op ≫
      (affineDiagramIso F hFqc).hom.app j.unop, ?_⟩
    have hcancel := congrArg (fun m => eB.inv ≫ m ≫ eA.hom) key
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using
      hcancel.symm
  · -- the equalization
    have hex : ∀ g : B ⟶ F.obj i, ∃ ψ : (affineDiagram F hFqc).leftOp.obj (op i) ⟶ W,
        (pushforwardAlgebraFunctor S).map ψ.op
          = eB.hom ≫ g ≫ (affineDiagramIso F hFqc).inv.app i :=
      fun g => (hbij _).2 _
    obtain ⟨ψ₁, hψ₁⟩ := hex g₁
    obtain ⟨ψ₂, hψ₂⟩ := hex g₂
    have hπψ : (Cone.mk L π).π.app (op i) ≫ ψ₁ = (Cone.mk L π).π.app (op i) ≫ ψ₂ := by
      refine (hbij L).1 ?_
      show (pushforwardAlgebraFunctor S).map (π.app (op i) ≫ ψ₁).op
        = (pushforwardAlgebraFunctor S).map (π.app (op i) ≫ ψ₂).op
      rw [op_comp, op_comp, (pushforwardAlgebraFunctor S).map_comp,
        (pushforwardAlgebraFunctor S).map_comp, hψ₁, hψ₂, hcompat i]
      have hstep : ∀ g : B ⟶ F.obj i, (eB.hom ≫ g ≫ (affineDiagramIso F hFqc).inv.app i) ≫
          ((affineDiagramIso F hFqc).hom.app i ≫ t.app i ≫ eA.inv)
            = eB.hom ≫ (g ≫ t.app i) ≫ eA.inv := by
        intro g
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      show (eB.hom ≫ g₁ ≫ (affineDiagramIso F hFqc).inv.app i) ≫
          ((affineDiagramIso F hFqc).hom.app i ≫ t.app i ≫ eA.inv)
            = (eB.hom ≫ g₂ ≫ (affineDiagramIso F hFqc).inv.app i) ≫
          ((affineDiagramIso F hFqc).hom.app i ≫ t.app i ≫ eA.inv)
      rw [hstep g₁, hstep g₂, hg]
    obtain ⟨k, w, hw⟩ := exists_map_comp_eq_of_isLimitPreservingOnAffineTransitions H
      ((affineDiagram F hFqc).leftOp) (isAffineHom_affineDiagram_leftOp_map hFqc)
      (compactSpace_affineDiagram_leftOp hFqc) (quasiSeparatedSpace_affineDiagram_leftOp hFqc)
      (Cone.mk L π) hπ (op i) ψ₁ ψ₂ hπψ
    refine ⟨k.unop, w.unop, w.unop, ?_⟩
    have hmap := congrArg (fun m => (pushforwardAlgebraFunctor S).map m.op) hw
    simp only [op_comp, (pushforwardAlgebraFunctor S).map_comp, hψ₁, hψ₂] at hmap
    have hnat := (affineDiagramIso F hFqc).hom.naturality w.unop
    have hcancel := congrArg
      (fun m => eB.inv ≫ m ≫ (affineDiagramIso F hFqc).hom.app k.unop) hmap
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at hcancel
    have hrw : ∀ g : B ⟶ F.obj i,
        g ≫ (affineDiagramIso F hFqc).inv.app i ≫
            ((affineDiagram F hFqc) ⋙ pushforwardAlgebraFunctor S).map w.unop ≫
              (affineDiagramIso F hFqc).hom.app k.unop
          = g ≫ F.map w.unop := by
      intro g
      rw [hnat]
      simp only [← Category.assoc, Iso.inv_hom_id_app]
      simp
    have hbridge : (pushforwardAlgebraFunctor S).map ((affineDiagram F hFqc).leftOp.map w).op
        = ((affineDiagram F hFqc) ⋙ pushforwardAlgebraFunctor S).map w.unop := rfl
    rwa [hbridge, hrw g₁, hrw g₂] at hcancel

end

end Stacks.AlgebraicGeometry.Tag0817Presentable

end
