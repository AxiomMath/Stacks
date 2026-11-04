module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas

/-!
# The completion of an affine chart along a closed subspace is a completion along an ideal

Let `S` be a scheme contained in a big fppf site `B`, let `W = Spec A` be an affine object of
the big fppf site of `S` and let `G ⊆ W` be a closed subspace, cut out by the ideal
`K = closedChartRingIdeal ⊆ A`. This file closes the colimit step left open in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart`: the cocone
`AlgebraicGeometry.Space.chartNeighbourhoodCocone` exhibiting each infinitesimal neighbourhood
`Spec (A ⧸ K ^ (n + 1))` inside the union of the infinitesimal neighbourhoods is a colimit
cocone, so that the completion `W^∧_G` of Stacks 0GXU is the completion
`AlgebraicGeometry.FormalSpace.completionAlongIdeal` of `Spec A` along the closed subscheme of
`K`.

## Main results

* `AlgebraicGeometry.Space.chartNeighbourhoodIsColimit`: the cocone of the infinitesimal
  neighbourhoods inside their union is a colimit cocone of presheaves.
* `AlgebraicGeometry.Space.completionSubspaceIsoCompletionAlongIdeal`: the completion of an
  affine chart along a closed subspace is the completion along the cutting-out ideal. This is
  the chart-level input of **Stacks 0GXX** to the omitted proof of **Stacks 0GXY**.
* `AlgebraicGeometry.Space.exists_iso_affineOver`: an affine object of the site is
  `AlgebraicGeometry.FormalSpace.affineOver` of its ring of regular functions, up to an
  isomorphism of the site, and `AlgebraicGeometry.Space.isIso_completionSubspaceMap` transports
  a completion along such an isomorphism, so
  `AlgebraicGeometry.Space.nonempty_completionSubspaceIsoCompletionAlongIdeal` applies to an
  arbitrary affine chart of the site, not only to one already presented as `affineOver`.
* `AlgebraicGeometry.Space.fg_closedChartIdeal_of_isLocallyOfFinitePresentation`: the ideal
  cutting out a closed subspace of finite presentation on an affine chart is finitely
  generated, which is the chart-level reading of the hypothesis of clause (2) of Stacks 0GXY.

The three clauses of Stacks 0GXY are assembled from these statements, with the atlas of `X` and
the set-theoretic condition of Stacks 0AIS proved rather than assumed, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAtlas`.

## Implementation notes

The colimit is produced by hand rather than through
`CategoryTheory.Limits.evaluationJointlyReflectsColimits`: the descent map out of the union is
written down directly, using the chosen factorization
`AlgebraicGeometry.Space.chartUnionFactor` of a section of the union through a neighbourhood,
and all three fields of `CategoryTheory.Limits.IsColimit` reduce to the one statement that the
legs of a cocone do not see which factorization was chosen, which is
`AlgebraicGeometry.Space.cocone_app_eq_of_comp_eq`. That statement in turn is the two halves of
the chart description of the completion: the neighbourhoods are monomorphisms
(`AlgebraicGeometry.Space.mono_quotientToAffineOver`), so two factorizations of one section
agree after passing to a common neighbourhood, and the transitions of the diagram are
compatible with the inclusions into the chart
(`AlgebraicGeometry.Space.quotientOverTransition_comp_quotientToAffineOver`).

Passing from presheaves to sheaves is then sheafification, which preserves colimits because it
is a left adjoint; the only wrinkle is that the completion of Stacks 0GXU is defined by the
explicit sheafification `CategoryTheory.GrothendieckTopology.sheafify` while
`AlgebraicGeometry.FormalSpace.completionAlongIdeal` is a colimit of the sheafified Yoneda
images, so the two sheafification functors are matched up by
`AlgebraicGeometry.Space.presheafToSheafIsoPlusPlus`.

## References

* [Stacks Project, Tag 0GXY](https://stacks.math.columbia.edu/tag/0GXY)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-! ### The legs of a cocone do not see the chosen factorization -/

section WellDefined

variable {K : Ideal A}

/-- **The legs of a cocone do not see the chosen factorization**, for two neighbourhoods in
increasing order: a section of the chart factoring through the `n`-th and the `m`-th
infinitesimal neighbourhood of the closed subscheme of `K` has the same image under the two
legs of any cocone over the diagram of neighbourhoods. -/
theorem cocone_app_eq_of_comp_eq_of_le
    (s : Cocone (infinitesimalNeighbourhoodDiagram B S hS str hA K ⋙
      BigAffineFppf.inclusion B S hS ⋙ uliftYoneda.{u + 1}))
    {V : (BigFppfOver B S hS)ᵒᵖ} {n m : ℕ} (hnm : n ≤ m)
    (t : V.unop ⟶ (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA (K ^ (n + 1))))
    (t' : V.unop ⟶ (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA (K ^ (m + 1))))
    (h : t ≫ quotientToAffineOver B S hS str hA (K ^ (n + 1)) =
      t' ≫ quotientToAffineOver B S hS str hA (K ^ (m + 1))) :
    (s.ι.app (ULift.up n)).app V (ULift.up t) =
      (s.ι.app (ULift.up m)).app V (ULift.up t') := by
  have hle : K ^ (m + 1) ≤ K ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  let g : (ULift.up n : ULift.{u + 1} ℕ) ⟶ ULift.up m :=
    homOfLE (show (ULift.up n : ULift.{u + 1} ℕ) ≤ ULift.up m from hnm)
  have hmono := mono_quotientToAffineOver B S hS str hA (K ^ (m + 1))
  have hcomp := quotientOverTransition_comp_quotientToAffineOver B S hS str hA hle
  have ht : t ≫ (BigAffineFppf.inclusion B S hS).map
      ((infinitesimalNeighbourhoodDiagram B S hS str hA K).map g) = t' := by
    refine (cancel_mono (quotientToAffineOver B S hS str hA (K ^ (m + 1)))).1 ?_
    refine Eq.trans (Category.assoc _ _ _) (Eq.trans ?_ h)
    exact congrArg (fun φ ↦ t ≫ φ) hcomp
  conv_lhs => rw [← s.w g]
  rw [NatTrans.comp_app]
  exact congrArg ((s.ι.app (ULift.up m)).app V) (congrArg ULift.up ht)

/-- **The legs of a cocone do not see the chosen factorization.** -/
theorem cocone_app_eq_of_comp_eq
    (s : Cocone (infinitesimalNeighbourhoodDiagram B S hS str hA K ⋙
      BigAffineFppf.inclusion B S hS ⋙ uliftYoneda.{u + 1}))
    {V : (BigFppfOver B S hS)ᵒᵖ} {n m : ℕ}
    (t : V.unop ⟶ (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA (K ^ (n + 1))))
    (t' : V.unop ⟶ (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA (K ^ (m + 1))))
    (h : t ≫ quotientToAffineOver B S hS str hA (K ^ (n + 1)) =
      t' ≫ quotientToAffineOver B S hS str hA (K ^ (m + 1))) :
    (s.ι.app (ULift.up n)).app V (ULift.up t) =
      (s.ι.app (ULift.up m)).app V (ULift.up t') := by
  rcases le_total n m with hnm | hnm
  · exact cocone_app_eq_of_comp_eq_of_le B S hS str hA s hnm t t' h
  · exact (cocone_app_eq_of_comp_eq_of_le B S hS str hA s hnm t' t h.symm).symm

end WellDefined

/-! ### The union of the infinitesimal neighbourhoods is their colimit -/

section Colimit

variable (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
  (hG : IsClosedSubspace B S hS G)

/-- The morphism out of the union of the infinitesimal neighbourhoods into the vertex of a
cocone over the neighbourhoods: send a section of the union to the image of a chosen
factorization of it through a neighbourhood. -/
def chartNeighbourhoodDesc (s : Cocone (chartNeighbourhoodDiagram B S hS str hA G hG)) :
    chartUnionFunctor B S hS str hA G ⟶ s.pt where
  app V := ↾fun x ↦ (s.ι.app (ULift.up (chartUnionIndex B S hS str hA G hG x))).app V
    (ULift.up (chartUnionFactor B S hS str hA G hG x))
  naturality := by
    intro V V' i
    ext x
    dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
    refine Eq.trans ?_ (NatTrans.naturality_apply
      (s.ι.app (ULift.up (chartUnionIndex B S hS str hA G hG x))) i _)
    refine cocone_app_eq_of_comp_eq B S hS str hA s _
      (i.unop ≫ chartUnionFactor B S hS str hA G hG x) ?_
    refine (chartUnionFactor_spec B S hS str hA G hG _).trans (Eq.symm ?_)
    exact (Category.assoc _ _ _).trans
      (congrArg (fun φ ↦ i.unop ≫ φ) (chartUnionFactor_spec B S hS str hA G hG x))

/-- **The union of the infinitesimal neighbourhoods of a closed subspace of an affine chart is
their colimit**, as presheaves of `Type (u + 1)` on the big fppf site. -/
def chartNeighbourhoodIsColimit :
    IsColimit (chartNeighbourhoodCocone B S hS str hA G hG) where
  desc s := chartNeighbourhoodDesc B S hS str hA G hG s
  fac s n := by
    ext V y
    exact cocone_app_eq_of_comp_eq B S hS str hA s _ y.down
      (chartUnionFactor_spec B S hS str hA G hG _)
  uniq s w hw := by
    ext V x
    have hx : (chartNeighbourhoodLeg B S hS str hA G hG
        (ULift.up (chartUnionIndex B S hS str hA G hG x))).app V
        (ULift.up (chartUnionFactor B S hS str hA G hG x)) = x :=
      Subtype.ext (congrArg ULift.up (chartUnionFactor_spec B S hS str hA G hG x))
    refine Eq.trans (congrArg (w.app V) hx.symm) ?_
    exact ConcreteCategory.congr_hom
      (congr_app (hw (ULift.up (chartUnionIndex B S hS str hA G hG x))) V) _

end Colimit

/-! ### The chart-level isomorphism -/

section Sheafify

attribute [local instance] FormalSpace.sheaf_hasColimits

variable (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
  (hG : IsClosedSubspace B S hS G)

/-- **The completion of an affine chart along a closed subspace is the completion along the
cutting-out ideal.** This is the chart-level step of the omitted proof of Stacks 0GXY: it is
what makes Stacks 0GXX applicable to the members of the atlas of `X^∧_Z`. -/
def completionSubspaceIsoCompletionAlongIdeal :
    completionSubspace B S hS ((schemeSpaceFunctor B S hS).obj (affineOver B S hS hA str)) G ≅
      completionAlongIdeal B S hS str hA (closedChartRingIdeal B S hS str hA G hG) :=
  ((presheafToSheafIsoPlusPlus B S hS).app (chartUnionFunctor B S hS str hA G)).symm ≪≫
    (isColimitOfPreserves (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
        (chartNeighbourhoodIsColimit B S hS str hA G hG)).coconePointUniqueUpToIso
      (colimit.isColimit _)

end Sheafify

/-! ### The chart ideal of a closed subspace of finite presentation -/

section FinitePresentation

private instance : MorphismProperty.IsStableUnderComposition (etaleOnSite B S hS) where
  comp_mem {_ _ _} p q hp hq := by
    have hp' : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) := hp
    have hq' : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) := hq
    change _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (p ≫ q))
    rw [Functor.map_comp]
    infer_instance

private instance : (etaleOnSite B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.Etale) (sq.map (BigFppfOver.toScheme B S hS)) hg

/-- The base-change map `CategoryTheory.Subfunctor.fromPreimage` along an étale morphism of
presheaves is étale. -/
private theorem etaleOnSite_presheaf_fromPreimage {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) (b : G ⟶ F) (hb : (etaleOnSite B S hS).presheaf b) :
    (etaleOnSite B S hS).presheaf (Z.fromPreimage b) :=
  (MorphismProperty.relative_isStableUnderBaseChange (etaleOnSite B S hS)).of_isPullback
    (Subfunctor.isPullback_preimage b Z).flip hb

/-- **A property holding on every étale chart of a subspace holds on every étale chart of its
inverse image** along an étale morphism of presheaves: an étale chart square of the inverse
image becomes one of the subspace itself, after composing the chart of the ambient presheaf
with the morphism and the chart of the inverse image with the base-change map
`CategoryTheory.Subfunctor.fromPreimage`, which is étale because Stacks 083Q exhibits it as a
base change of the morphism. -/
theorem holdsOnEveryEtaleChart_preimage_ι (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor F) (b : G ⟶ F)
    (hb : (etaleOnSite B S hS).presheaf b)
    (h : HoldsOnEveryEtaleChart B S hS P Z.ι) :
    HoldsOnEveryEtaleChart B S hS P (Z.preimage b).ι := by
  have hiso : (etaleOnSite B S hS).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  intro U V a c k ha hc hsq
  refine h U V (a ≫ Z.fromPreimage b) (c ≫ b) k
    (MorphismProperty.comp_mem _ _ _ ha (etaleOnSite_presheaf_fromPreimage B S hS Z b hb))
    (MorphismProperty.comp_mem _ _ _ hc hb) ?_
  rw [reassoc_of% hsq, Category.assoc, Subfunctor.fromPreimage_ι]

/-- **The ideal cutting out a closed subspace of finite presentation on an affine chart is
finitely generated.** Over an affine object `V` of the site and an étale chart `b` of the
ambient presheaf, the inverse image of the subspace is cut out by a closed immersion of
schemes, which local finite presentation of the subspace makes locally of finite presentation
because that closed immersion sits in an étale chart square of the subspace; the case of
schemes, Stacks 01TV, then finitely generates its ideal over the affine opens of the chart, and
the chart being affine the top one is among them. -/
theorem fg_closedChartIdeal_of_isLocallyOfFinitePresentation
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor F)
    (hfp : IsLocallyOfFinitePresentation B S hS Z.ι) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (b : yoneda.obj V ⟶ F)
    (hb : (etaleOnSite B S hS).presheaf b)
    (hG : IsClosedSubspace B S hS (Z.preimage b)) :
    (closedChartIdeal B S hS (Z.preimage b) hG).FG := by
  have he : IsIso (hG.2.rep.fst (𝟙 (yoneda.obj V))) := isIso_rep_fst_id B S hS _ hG
  have ha : (etaleOnSite B S hS).presheaf
      (hG.2.rep.fst (𝟙 (yoneda.obj V)) ≫ Z.fromPreimage b) := by
    have : (etaleOnSite B S hS).presheaf.RespectsIso :=
      MorphismProperty.relative_respectsIso (etaleOnSite B S hS)
    exact ((etaleOnSite B S hS).presheaf.cancel_left_of_respectsIso
      (hG.2.rep.fst (𝟙 (yoneda.obj V))) (Z.fromPreimage b)).2
      (etaleOnSite_presheaf_fromPreimage B S hS Z b hb)
  have hsq : yoneda.map (closedChartHom B S hS (Z.preimage b) hG) ≫ b =
      (hG.2.rep.fst (𝟙 (yoneda.obj V)) ≫ Z.fromPreimage b) ≫ Z.ι := by
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
      rep_fst_id_comp_ι B S hS (Z.preimage b) hG]
  have hP : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (closedChartHom B S hS (Z.preimage b) hG)) :=
    hfp _ V _ b (closedChartHom B S hS (Z.preimage b) hG) ha hb hsq
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (closedChartHom B S hS (Z.preimage b) hG)) :=
    isClosedImmersion_closedChartHom B S hS (Z.preimage b) hG
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (closedChartObj B S hS (Z.preimage b) hG)) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map (closedChartHom B S hS (Z.preimage b) hG))).1
  have hfg := (_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker _).1 hP
    ⟨⊤, isAffineOpen_top _⟩
  rw [Scheme.ker_of_isAffine] at hfg
  simpa [Scheme.IdealSheafData.ofIdealTop_ideal, closedChartIdeal] using hfg

end FinitePresentation

/-! ### An arbitrary affine chart of the site -/

section AnyAffineChart

attribute [local instance] FormalSpace.sheaf_hasColimits

/-- **An affine object of the big fppf site is `affineOver` of its ring of regular
functions**, up to an isomorphism of the site: the isomorphism `W ≅ Spec Γ(W, ⊤)` of an affine
scheme lifts to the site because it commutes with the structure morphism to `S`, and
`Spec Γ(W, ⊤)` is again in the site because the size of a scheme is an isomorphism
invariant. The ring is the ring of regular functions of the chart, so it is Noetherian as soon
as the chart is locally Noetherian; that is recorded here rather than in a second lemma
because it is a property of the particular ring produced. -/
theorem exists_iso_affineOver (W : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (.of A)))
      (str : Spec (.of A) ⟶ S),
      (∀ _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W),
        IsNoetherianRing A) ∧
      Nonempty (affineOver B S hS hA str ≅ W) := by
  let X : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj W
  have hXaff : IsAffine X := inferInstanceAs
    (IsAffine ((BigFppfOver.toScheme B S hS).obj W))
  let A : Type u := Γ(X, ⊤)
  let e : X ≅ Spec (CommRingCat.of A) := X.isoSpec
  have hA : B.Contains (Spec (CommRingCat.of A)) := by
    show (Spec (CommRingCat.of A)).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact W.left.property
  let str : Spec (CommRingCat.of A) ⟶ S := e.inv ≫ B.inclusion.map W.hom
  let eSite : (B.obj hA : B.Schemes) ≅ W.left :=
    { hom := ObjectProperty.homMk (show Spec (CommRingCat.of A) ⟶ X from e.inv)
      inv := ObjectProperty.homMk (show X ⟶ Spec (CommRingCat.of A) from e.hom)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact e.inv_hom_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact e.hom_inv_id }
  have htri : eSite.hom ≫ W.hom = (affineOver B S hS hA str).hom := by
    apply ObjectProperty.hom_ext
    rfl
  exact ⟨A, inferInstance, hA, str, fun hN ↦ hN.component_noetherian ⟨⊤, isAffineOpen_top X⟩,
    ⟨Over.isoMk eSite htri⟩⟩

/-- **The morphism of completions induced by an isomorphism of the ambient algebraic space is
an isomorphism**, being a base change of one along the completion square of Stacks 0GXV. -/
theorem isIso_completionSubspaceMap {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (Z : Subfunctor X.1) [IsIso f.hom] :
    IsIso (completionSubspaceMap B S hS f Z) := by
  have hf : IsIso (sheafifiedULiftMap B S hS f.hom) := by
    refine ⟨sheafifiedULiftMap B S hS (inv f.hom), ?_, ?_⟩
    · rw [← sheafifiedULiftMap_comp, IsIso.hom_inv_id, sheafifiedULiftMap_id]
    · rw [← sheafifiedULiftMap_comp, IsIso.inv_hom_id, sheafifiedULiftMap_id]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms (FormalSpace.FppfSheaf B S hS))
    (isPullback_completionSubspaceMap B S hS f Z) hf

/-- **The completion of an arbitrary affine chart of the site along a closed subspace is a
completion along an ideal.** This is the form in which the chart-level step of the omitted
proof of Stacks 0GXY applies to the members of an affine atlas: the chart need not be
presented as `AlgebraicGeometry.FormalSpace.affineOver`, since the completion is transported
along the normalizing isomorphism of the site.

Two properties of the ring and the ideal produced are recorded alongside, because they are
properties of the particular normalization chosen rather than separate statements: the ring is
Noetherian as soon as the chart is locally Noetherian, and the ideal is finitely generated as
soon as the closed subspace is locally of finite presentation over the chart, by
`AlgebraicGeometry.Space.fg_closedChartIdeal_of_isLocallyOfFinitePresentation`. -/
theorem nonempty_completionSubspaceIsoCompletionAlongIdeal (W : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G) :
    ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
      (hA : B.Contains (Spec (.of A))) (K : Ideal A),
      (∀ _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W),
        IsNoetherianRing A) ∧
      (∀ _ : IsLocallyOfFinitePresentation B S hS G.ι, K.FG) ∧
      Nonempty (completionSubspace B S hS ((schemeSpaceFunctor B S hS).obj W) G ≅
        completionAlongIdeal B S hS str hA K) := by
  obtain ⟨A, hCR, hA, str, hNoeth, ⟨e⟩⟩ := exists_iso_affineOver B S hS W
  let : CommRing A := hCR
  have hG' : IsClosedSubspace B S hS (G.preimage (yoneda.map e.hom)) :=
    isClosedSubspace_preimage B S hS (yoneda.map e.hom) G
      (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hA str)) hG
  have : IsIso ((schemeSpaceFunctor B S hS).map e.hom).hom := by
    show IsIso (yoneda.map e.hom)
    infer_instance
  have := isIso_completionSubspaceMap B S hS ((schemeSpaceFunctor B S hS).map e.hom) G
  have hEtale : (etaleOnSite B S hS).presheaf (yoneda.map e.hom) :=
    MorphismProperty.relative_map_iff.2
      (show _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map e.hom) from
        inferInstance)
  exact ⟨A, hCR, str, hA,
    closedChartRingIdeal B S hS str hA (G.preimage (yoneda.map e.hom)) hG', hNoeth,
    fun hfp ↦ Ideal.FG.map (fg_closedChartIdeal_of_isLocallyOfFinitePresentation B S hS G hfp
      (yoneda.map e.hom) hEtale hG') _,
    ⟨(asIso (completionSubspaceMap B S hS ((schemeSpaceFunctor B S hS).map e.hom) G)).symm ≪≫
      completionSubspaceIsoCompletionAlongIdeal B S hS str hA (G.preimage (yoneda.map e.hom)) hG'⟩⟩

end AnyAffineChart

end AlgebraicGeometry.Space

end
