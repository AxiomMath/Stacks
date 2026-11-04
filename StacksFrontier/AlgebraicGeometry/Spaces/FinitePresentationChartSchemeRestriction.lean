module

public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections

/-!
# Finite presentation of the sections of the chart restriction of a module on an algebraic space

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, and let `M` be a
quasi-coherent `𝒪_X`-module of finite presentation on the small étale site of `X`.  The file
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean` transports
**coherence** of `M` to the chart restriction
`AlgebraicGeometry.Space.chartSchemeModule` over a Noetherian affine chart; this file transports
**finite presentation of the module of global sections** over an affine chart, with no Noetherian
hypothesis anywhere.

## Main results

* `Stacks.SheafOfModules.finitePresentation_sections_pushforward`: finite presentation of sections
  passes to a pushforward of sheaves of modules along a continuous functor, when the structure map
  is bijective at the object.
* `Stacks.SheafOfModules.finitePresentation_sections_of_iso`: finite presentation of sections is
  invariant under isomorphism of sheaves of modules.
* `AlgebraicGeometry.Space.finitePresentation_sectionsTop_chartSchemeModule`: **over an affine
  chart the global sections of the chart restriction form a finitely presented module over the
  global functions of the chart's scheme.**

## Implementation notes

The three statements mirror `Stacks.SheafOfModules.moduleFinite_sections_pushforward`,
`Stacks.SheafOfModules.moduleFinite_sections_of_iso` and
`AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule` of the coherence file (the
ring-level `Stacks.Module.finite_of_surjective_of_smul_eq` is mirrored by
`Stacks.Module.finitePresentation_of_bijective_of_smul_eq`), along the same chain of four
pushforwards — the slice at the chart, the comparison of Stacks 04M0, the
comparison of the representable case of Stacks 03ED, and the inclusion of the small Zariski site
— with the base case `AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent` replaced by
`AlgebraicGeometry.Space.module_finitePresentation_sections_of_isFinitePresentationOnSite`.

**The mirror is not literal at one point: surjectivity of the comparison ring maps is not
enough.**  Finiteness of a module descends along a bare surjection of rings, because a spanning
set downstairs spans upstairs; the relations do not descend, and over a surjection with a
kernel that is not finitely generated finite presentation genuinely fails — see
`Stacks.Module.finitePresentation_of_bijective_of_smul_eq`, which carries the counterexample.
What the chain supplies is more than surjectivity: each of its four comparison maps is an
isomorphism of rings.  Two of them are identities, and the other two are recorded as bijective by
`Stacks.SheafOfModules.bijective_reindexBackSharp_app` and
`AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app`.  So the hypothesis of the
pushforward step here is bijectivity, not surjectivity, and nothing is lost.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules

universe w m v₁ v₂ u₁ u₂

open CategoryTheory

/-- **Finite presentation of sections passes to a pushforward of sheaves of modules.**  The
sections over `A` of the pushforward of `N` along a continuous functor `F` and a morphism of
sheaves of rings `φ` are the sections of `N` over `F.obj A`, with scalars restricted along `φ`;
so they are finitely presented as soon as those are and `φ` is bijective at `A`.

This is the finite-presentation form of
`Stacks.SheafOfModules.moduleFinite_sections_pushforward`, and it asks for bijectivity where that
asks only for surjectivity: see the module documentation. -/
theorem finitePresentation_sections_pushforward {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
    [F.IsContinuous J K] (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (N : _root_.SheafOfModules.{m} R) (A : C)
    (hφ : Function.Bijective (φ.hom.app (Opposite.op A)).hom)
    (h : Module.FinitePresentation (R.obj.obj (Opposite.op (F.obj A)))
      (N.val.obj (Opposite.op (F.obj A)))) :
    Module.FinitePresentation (S.obj.obj (Opposite.op A))
      (((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (Opposite.op A)) :=
  @Stacks.Module.finitePresentation_of_bijective_of_smul_eq _ _ _ _ _ _
    (((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (Opposite.op A)).isModule
    (N.val.obj (Opposite.op (F.obj A))).isModule (φ.hom.app (Opposite.op A)).hom hφ
    (fun _ _ => rfl) h

/-- **Finite presentation of sections is invariant under isomorphism.**  An isomorphism of sheaves
of modules induces a linear isomorphism of the sections over every object. -/
theorem finitePresentation_sections_of_iso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{w}}
    {F G : _root_.SheafOfModules.{m} R} (e : F ≅ G) (A : C)
    (h : Module.FinitePresentation (R.obj.obj (Opposite.op A)) (G.val.obj (Opposite.op A))) :
    Module.FinitePresentation (R.obj.obj (Opposite.op A)) (F.val.obj (Opposite.op A)) :=
  have e' : F.val.obj (Opposite.op A) ≅ G.val.obj (Opposite.op A) :=
    { hom := e.hom.val.app (Opposite.op A)
      inv := e.inv.val.app (Opposite.op A)
      hom_inv_id := congrArg (fun k : F ⟶ F => k.val.app (Opposite.op A)) e.hom_inv_id
      inv_hom_id := congrArg (fun k : G ⟶ G => k.val.app (Opposite.op A)) e.inv_hom_id }
  have := h
  Module.FinitePresentation.of_equiv e'.toLinearEquiv.symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-- **The global sections of the chart restriction of a module of finite presentation are finitely
presented.**  For a quasi-coherent `𝒪_X`-module of finite presentation on the small étale site and
an affine étale chart, the global sections of the `AlgebraicGeometry.Scheme.Modules` which `M`
becomes on the chart's scheme form a finitely presented module over the global functions of that
scheme.  No Noetherian hypothesis.

The chain of four pushforwards — the slice at the chart, the comparison of Stacks 04M0, the
comparison of the representable case of Stacks 03ED, and the inclusion of the small Zariski site
— identifies those global sections with the sections of `M` over the étale chart
`AlgebraicGeometry.Space.openChartOfComparison … ⊤`, whose scheme is affine, and there the
sections are finitely presented by
`AlgebraicGeometry.Space.module_finitePresentation_sections_of_isFinitePresentationOnSite`.

This is the finite-presentation mirror of
`AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule`. -/
theorem finitePresentation_sectionsTop_chartSchemeModule
    (hM : M.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite M)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V)) :
    Module.FinitePresentation
      ((chartScheme V).ringCatSheaf.obj.obj (op (⊤ : (chartScheme V).Opens)))
      ((chartSchemeModule B S hS X M hM V).val.obj (op (⊤ : (chartScheme V).Opens))) := by
  let U := _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
    (chartScheme V) (chartFppfObject B S hS X V).left.property ⊤
  have h0 := module_finitePresentation_sections_of_isFinitePresentationOnSite
    (B := B) (S := S) (hS := hS) (F := X.1) (hF := X.2) M
    hM hfp (openChartOfComparison B S hS X V ⊤)
    (isAffine_chartScheme_openChartOfComparison_top B S hS X V hV)
  have h1 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (𝟙 ((structureRingSheaf B S hS X).over V)) M
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.obj
      ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj U))
    Function.bijective_id h0
  have h2 := @Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) inferInstance
    (Over V) inferInstance
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over V)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor
    (chartStructureRingSheaf B S hS X V) ((structureRingSheaf B S hS X).over V)
    (isContinuous_chartLocalization_chartSpace B S hS X V)
    (𝟙 (chartStructureRingSheaf B S hS X V)) (M.over V)
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj U)
    Function.bijective_id h1
  have h3 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X V)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X V)))
    (chartSmallEtaleRestriction B S hS X M V)
    U
    (Stacks.SheafOfModules.bijective_reindexBackSharp_app _ _ _) h2
  have h4 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) (chartScheme V)
      (chartFppfObject B S hS X V).left.property)
    (chartSchemeEtaleModule B S hS X M hM V)
    (⊤ : (chartScheme V).Opens)
    (_root_.AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app _ _ _ _) h3
  exact Stacks.SheafOfModules.finitePresentation_sections_of_iso
    (chartSchemeModuleIsoRestrictModule B S hS X M hM V) ⊤ h4

end AlgebraicGeometry.Space

end
