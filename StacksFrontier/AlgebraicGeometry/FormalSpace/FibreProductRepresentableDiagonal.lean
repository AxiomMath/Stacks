module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.AffineThickeningULift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products of formal algebraic spaces over a sheaf with representable diagonal

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AJ2**: let `X` and `Y` be formal
algebraic spaces over `S` and let `Z` be a sheaf on `(Sch/S)_fppf` whose diagonal is
representable by algebraic spaces. Then for maps of sheaves `X ⟶ Z` and `Y ⟶ Z` the fibre
product `X ×_Z Y` is a formal algebraic space.

## Main results

* `FormalSpace.isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_representableDiagonal`:
  the case where `X` and `Y` are affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representableDiagonal`:
  **Stacks 0AJ2**, the fibre product `X ×_Z Y` of formal algebraic spaces is a formal algebraic
  space.

## Implementation notes

The proof is the one of the source. Affine étale coverings of `X` and `Y` reduce the statement
to affine formal algebraic spaces (Stacks 0AJ1), by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages`. For
`X = colim Spec A_λ` and `Y = colim Spec B_μ`, the fibre product is the colimit of the
algebraic spaces `Spec A_λ ×_Z Spec B_μ` along thickenings, each transition being the
composite of a base change of `Spec A_λ ⟶ Spec A_λ'` with a base change of
`Spec B_μ ⟶ Spec B_μ'`; and that colimit is a formal algebraic space by the argument of
Stacks 0AIU,
`AlgebraicGeometry.FormalSpace.DependentProduct.isFormalAlgebraicSpace_colimit_of_affineStages`.
The étale charts of the least stage are transported to the colimit by the dependent product
along the colimit injection, which is representable étale by Stacks 039R, and their stages are
affine because each is a thickening over an affine scheme of an affine scheme — twice, once for
each of the two coordinates — which is
`AlgebraicGeometry.FormalSpace.DependentProduct.exists_iso_uliftYoneda_liftAlong_comp`.

The set-theoretic condition of Stacks 0AIS on the fibre product is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback_of_representableDiagonal`.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The transitions of the diagram of relative products of the stages of two presentations
are thickenings after base change along points**: each is a base change of a transition of the
first presentation followed by a base change of a transition of the second. -/
theorem relative_isThickening_relativeProductDiagram_map {I₁ I₂ : Type (u + 1)}
    [Preorder I₁] [Preorder I₂] (D₁ : I₁ ⥤ BigAffineFppf B S hS) (D₂ : I₂ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j), IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (hD₂ : ∀ ⦃i j : I₂⦄ (f : i ⟶ j), IsThickening ((BigAffineFppf.toScheme B S hS).map (D₂.map f)))
    (c₁ : Cocone (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}))
    (c₂ : Cocone (D₂ ⋙ BigAffineFppf.inclusion B S hS ⋙
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}))
    {Z : FppfSheaf B S hS} (a : c₁.pt ⟶ Z) (b : c₂.pt ⟶ Z) {p q : I₁ × I₂} (f : p ⟶ q) :
    (MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}
      ((Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)).map f) := by
  have : (MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@IsThickening : MorphismProperty Scheme.{u})
  have : (MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have : ((MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : ((MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  rw [uncurry_relativeProductDiagram_map]
  refine MorphismProperty.comp_mem _ _ _ ?_ ?_
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_relativeBaseTransition c₁ c₂ a b f.1 p.2).flip
      (MorphismProperty.relative_map (hD₁ f.1))
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (equifibered_relativeStageSnd c₁ c₂ a b q.1 f.2).flip
      (MorphismProperty.relative_map (hD₂ f.2))

/-- A presentation as a colimit of sheafified Yoneda sheaves gives one for the `uliftYoneda`
sheaves. -/
private theorem nonempty_iso_colimit_uliftYoneda
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)] {I : Type (u + 1)} [Preorder I]
    {X : FppfSheaf B S hS} (D : I ⥤ BigAffineFppf B S hS)
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1})) :=
  ⟨e ≪≫ HasColimit.isoOfNatIso (Functor.isoWhiskerLeft D (Functor.isoWhiskerLeft _
    (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).symm))⟩

/-- **The fibre product of two affine formal algebraic spaces over a sheaf whose diagonal is
representable by algebraic spaces is a formal algebraic space.** -/
theorem isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_representableDiagonal
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj))
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hset : SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
    satisfiesSetTheoreticCondition_pullback_of_representableDiagonal B S hS p q hZ hX.1
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX) hY.1
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY)
  obtain ⟨-, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨eX⟩⟩ := hX
  obtain ⟨-, I₂, pre₂, hne₂, hdir₂, D₂, hD₂, ⟨eY⟩⟩ := hY
  let : Preorder I₁ := pre₁
  let : Nonempty I₁ := hne₁
  let : IsDirected I₁ (· ≤ ·) := hdir₁
  let : Preorder I₂ := pre₂
  let : Nonempty I₂ := hne₂
  let : IsDirected I₂ (· ≤ ·) := hdir₂
  set Y' := J.uliftYoneda.{u + 1} with hY'
  set F₁ : I₁ ⥤ FppfSheaf B S hS := D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙ Y'
  set F₂ : I₂ ⥤ FppfSheaf B S hS := D₂ ⋙ BigAffineFppf.inclusion B S hS ⋙ Y'
  obtain ⟨eX'⟩ := nonempty_iso_colimit_uliftYoneda B S hS D₁ eX
  obtain ⟨eY'⟩ := nonempty_iso_colimit_uliftYoneda B S hS D₂ eY
  set c₁ := colimit.cocone F₁
  set c₂ := colimit.cocone F₂
  set a : c₁.pt ⟶ Z := eX'.inv ≫ p with ha
  set b : c₂.pt ⟶ Z := eY'.inv ≫ q
  have h₁ : IsUniversalColimit c₁ := sheaf_filteredColimit_isUniversalColimit J F₁
  have h₂ : IsUniversalColimit c₂ := sheaf_filteredColimit_isUniversalColimit J F₂
  set Θ := CategoryTheory.prodPreorderEquivalence I₁ I₂
  set Big := Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)
  set E₀ : CategoryTheory.ProdPreorder I₁ I₂ ⥤ FppfSheaf B S hS := Θ.functor ⋙ Big with hE₀
  have hE₀colim : IsColimit ((relativeProductCocone c₁ c₂ a b).whisker Θ.functor) :=
    (isColimit_relativeProductCocone c₁ c₂ a b h₁ h₂).whiskerEquivalence Θ
  -- the up-set of a base index, which has a least element
  obtain ⟨o₁⟩ := hne₁
  obtain ⟨o₂⟩ := hne₂
  set o : CategoryTheory.ProdPreorder I₁ I₂ := (o₁, o₂)
  set E : {j : CategoryTheory.ProdPreorder I₁ I₂ // o ≤ j} ⥤ FppfSheaf B S hS :=
    CategoryTheory.upSetInclusion o ⋙ E₀ with hE
  set o' : {j : CategoryTheory.ProdPreorder I₁ I₂ // o ≤ j} := ⟨o, le_refl o⟩
  have ho : ∀ n : {j : CategoryTheory.ProdPreorder I₁ I₂ // o ≤ j}, o' ≤ n := fun n ↦ n.2
  obtain ⟨hc⟩ := CategoryTheory.nonempty_isColimit_whiskerLeft_upSetInclusion o hE₀colim
  have hsq : IsPullback (pullback.fst a b ≫ eX'.inv) (pullback.snd a b ≫ eY'.inv) p q := by
    refine (IsPullback.of_hasPullback a b).of_iso (Iso.refl _) eX'.symm eY'.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact (Category.comp_id a).trans rfl
    · exact (Category.comp_id b).trans rfl
  have eP : pullback p q ≅ colimit E :=
    hsq.isoPullback.symm ≪≫ (hc.coconePointUniqueUpToIso (colimit.isColimit E))
  -- the transitions are thickenings after base change along points, and monomorphisms
  have hthick : ∀ ⦃n m : {j : CategoryTheory.ProdPreorder I₁ I₂ // o ≤ j}⦄ (f : n ⟶ m),
      (MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative Y' (E.map f) := fun n m f ↦
    relative_isThickening_relativeProductDiagram_map B S hS D₁ D₂ hD₁ hD₂ c₁ c₂ a b _
  have hmono : ∀ ⦃n m : {j : CategoryTheory.ProdPreorder I₁ I₂ // o ≤ j}⦄ (f : n ⟶ m),
      Mono (E.map f) := fun n m f ↦ DependentProduct.mono_of_relative_isThickening _ (hthick f)
  -- the stages are algebraic spaces
  have halg : ∀ (i : I₁) (j : I₂), Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b)).obj := fun i j ↦
    DependentProduct.isAlgebraicSpaceULift_pullback_of_representableDiagonal hZ _ _
  -- the stages of the charts are affine
  have hstage : ∀ {W : BigFppfOver B S hS}
      (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ E.obj o'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom →
      ∀ n, ∃ A : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Nonempty ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A ≅
          DependentProduct.liftAlong B S hS (E.map (homOfLE (ho n))) c) := by
    intro W c hW hc n
    have hn₁ : o₁ ≤ n.1.1 := n.2.1
    have hn₂ : o₂ ≤ n.1.2 := n.2.2
    exact DependentProduct.exists_iso_uliftYoneda_liftAlong_comp
      (relativeBaseTransition c₁ c₂ a b (homOfLE hn₁) o₂)
      (relativeStageTransition c₁ c₂ a b n.1.1 (homOfLE hn₂))
      (D₁.obj n.1.1).property (D₂.obj n.1.2).property
      ((BigAffineFppf.inclusion B S hS).map (D₁.map (homOfLE hn₁))) (hD₁ _)
      ((BigAffineFppf.inclusion B S hS).map (D₂.map (homOfLE hn₂))) (hD₂ _)
      _ _ (isPullback_relativeBaseTransition c₁ c₂ a b (homOfLE hn₁) o₂)
      _ _ (equifibered_relativeStageSnd c₁ c₂ a b n.1.1 (homOfLE hn₂))
      (halg _ _) (halg _ _) hW c hc
  have hsetE : SatisfiesSetTheoreticCondition B S hS (colimit E) :=
    satisfiesSetTheoreticCondition_of_iso B S hS eP hset
  exact isFormalAlgebraicSpace_of_iso B S hS eP
    (DependentProduct.isFormalAlgebraicSpace_colimit_of_affineStages ho E hmono hthick
      (halg o₁ o₂) hsetE hstage)

/-- **Stacks 0AJ2.** Let `S` be a scheme, let `X` and `Y` be formal algebraic spaces over `S` and
let `Z` be a sheaf on `(Sch/S)_fppf` whose diagonal is representable by algebraic spaces. For
maps of sheaves `p : X ⟶ Z` and `q : Y ⟶ Z`, the fibre product `X ×_Z Y` is a formal algebraic
space. -/
@[stacks 0AJ2]
theorem isFormalAlgebraicSpace_pullback_of_representableDiagonal
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj))
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  have hYrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY
  refine isFormalAlgebraicSpace_pullback_of_affineStages B S hS p q hX hY
    (fun _ _ p' q' hX' hY' ↦
      isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_representableDiagonal B S hS p' q'
        hZ hX' hY')
    (satisfiesSetTheoreticCondition_pullback_of_representableDiagonal B S hS p q hZ hX.1
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX) hY.1 hYrep)
    fun X' a hX' ↦ ?_
  have hPi : IsPullback (pullback.fst a (pullback.fst p q))
      (pullback.snd a (pullback.fst p q) ≫ pullback.snd p q) (a ≫ p) q :=
    (IsPullback.of_hasPullback a (pullback.fst p q)).paste_vert (IsPullback.of_hasPullback p q)
  exact satisfiesSetTheoreticCondition_of_iso B S hS hPi.isoPullback.symm
    (satisfiesSetTheoreticCondition_pullback_of_representableDiagonal B S hS (a ≫ p) q hZ hX'.1
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX') hY.1 hYrep)

end AlgebraicGeometry.FormalSpace

end
