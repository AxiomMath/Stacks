module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularSequenceFlatComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceFlatnessEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspacePullbackGerm
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingSmoothChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldValuedPointStackMorphismIso
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuasiFiniteChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.ZeroLocusChartBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The fibre of a chart base change over a lifted field-valued point (Stacks 06MD)

Let `𝒳` be an algebraic stack over `S`, let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space,
let `Spec k ⟶ 𝒳` be a field-valued point with fibre `F = U ×_𝒳 Spec k`, and let `c : 𝒲 ⟶ 𝒳` be a
surjective 1-morphism — in the application a smooth surjective chart. This file performs the one
step that separates the flatness conjunct of **Stacks 06MD** from the flatness half of
**Stacks 06LW**: it identifies the fibre of `U ×_𝒳 𝒲 ⟶ 𝒲` over a lifted field-valued point of
`𝒲` with a base change of `F`, and transports the regular-sequence hypothesis into it.

## Main results

* `AlgebraicGeometry.Stack.exists_chartFibre_isPullback_isRegular`: all the data **Stacks 06LW**
  asks of `U ×_𝒳 𝒲 ⟶ 𝒲` — a field-valued point of `𝒲`, a cartesian square presenting the fibre
  over it, a geometric point of that fibre, and the regularity of the pulled-back global
  functions at it — together with the fact that the geometric point sits over `p(z)` in `|U|`.

## How it is proved

The source lifts `Spec k ⟶ 𝒳` through the chart and observes that the resulting fibre `F'` of
`U ×_𝒳 𝒲 ⟶ 𝒲` is `F ×_{Spec k} Spec k'`. Here that observation is the comparison of two
2-fibre products of *one* cospan.

The lift is `AlgebraicGeometry.Stack.exists_fieldValuedPoint_lift_of_isSurjective`, applied to the
field-valued point of `𝒳` which `AlgebraicGeometry.Stack.tautologicalFieldValuedPoint` and
`AlgebraicGeometry.Stack.twoIso_fieldValuedPointStackMorphism_fieldValuedPointMap` read off the
given 1-morphism `Spec k ⟶ 𝒳`; it needs only surjectivity. The residue field is then enlarged once
more, by `AlgebraicGeometry.Stack.exists_geometricPoint_lift_fieldSpectrum`, so that the lift is
available at a *geometric* point of `F` over the prescribed point of `|F|`: that is what makes the
field of the statement the residue field of a geometric point, hence an object of the site on the
nose.

Both fibres are then 2-fibre products of the cospan `(f, Spec k' ⟶ Spec k ⟶ 𝒳)`, got by pasting
(`CategoryTheory.Bicategory.isTwoFibreProduct_paste`) the chart square, respectively the square of
`F`, with the square of the field extension, after
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` has moved the leg along the
2-isomorphism the lift produces. So
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct` compares the two
representing algebraic spaces compatibly with the projections to `U`, and
`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct` turns the inner square
on the chart side into the `IsPullback` which Stacks 06LW asks for.

The regularity hypothesis travels along that comparison by
`AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt` — an
isomorphism is flat — in the same way, and with the same two lemmas, that the proof of the
flatness half of Stacks 06LW moves it across its own enlargement of `k`. The passage from the
germs of `f₁, …, f_r` on `U` to the germs of the pulled-back functions on `U ×_𝒳 𝒲` is
`AlgebraicGeometry.Space.etaleLocalRingGerm_globalFunctionsMap` together with the functoriality
`AlgebraicGeometry.Space.etaleLocalRingMap_comp` of the comparison homomorphisms of
**Stacks 04NG**; no new statement about germs is needed.

No `@[stacks]` attribute is attached: this is the fibre identification inside the proof of
**Stacks 06MD**, whose covering declaration is in
`StacksFrontier/AlgebraicGeometry/Stacks/ChartSlicingFlatness.lean`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ChartSlicingLiftedFibre :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ChartSlicingLiftedFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (𝒳: AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable {r : ℕ}
  (a : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

variable (𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒳)
  (Wv : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
    (presheafOfCategories (Wv ⋙ typeToCat)).p)
  (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)

/-! ### The projection of the chart base change onto the chart -/

/-- The projection `U ×_𝒳 𝒲 ⟶ 𝒲` of **Stacks 04SW**, read as a morphism of algebraic spaces.
This is the morphism to which **Stacks 06LW** is applied. -/
abbrev chartBaseChangeChartProjection : P ⟶ Wv :=
  representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val 𝒲.val P Wv eP eW
    (twoFibreProductSquareAlgebraicStacks B S hS c f).fst.hom

/-- The structure morphism `F ⟶ Spec k` of the fibre `F = U ×_𝒳 Spec k`, read as a morphism of
algebraic spaces through **Stacks 04SW**. The companion of
`AlgebraicGeometry.Stack.fibreSpaceProjection`, which reads the other projection. -/
abbrev fibreSpaceStructureMorphism :
    Fsp ⟶ yoneda.obj (fieldPointObject B S hS k hk toBase) :=
  representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val
    (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val Fsp
    (yoneda.obj (fieldPointObject B S hS k hk toBase)) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom

/-! ### Two pasted 2-fibre products of one cospan -/

section Comparison

variable (𝒦 𝒯₀ : AlgebraicStacks.{u, w} B S hS) (g' : 𝒦 ⟶ 𝒳)
  (rr : 𝒯₀ ⟶ 𝒲) (ρρ : 𝒯₀ ⟶ 𝒦)
  (Kv Tv : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hTv : IsAlgebraicSpace B S hS Tv)
  (eK : StacksRepresentableCFG.EquivalenceOver 𝒦.val.val.p
    (presheafOfCategories (Kv ⋙ typeToCat)).p)
  (eT : StacksRepresentableCFG.EquivalenceOver 𝒯₀.val.val.p
    (presheafOfCategories (Tv ⋙ typeToCat)).p)
  (eFib : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS f g').pt.val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hFsp hTv hP in
/-- **The fibre of the chart base change and the base change of the fibre are isomorphic over
`U`.** Let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space, let `c : 𝒲 ⟶ 𝒳` and
`g' : 𝒦 ⟶ 𝒳` be two more, and let `𝒯₀` come with 1-morphisms `rr : 𝒯₀ ⟶ 𝒲` and `ρρ : 𝒯₀ ⟶ 𝒦`
whose composites to `𝒳` are 2-isomorphic. Then the 2-fibre products `(U ×_𝒳 𝒲) ×_𝒲 𝒯₀` and
`(U ×_𝒳 𝒦) ×_𝒦 𝒯₀` are both represented by algebraic spaces, each by a cartesian square of
representing algebraic spaces, and the two representing spaces are isomorphic compatibly with
their projections to `U`.

Both are 2-fibre products of the cospan `(f, ρρ ≫ g')` — the first after
`CategoryTheory.Bicategory.TwoCommSq.reindexSnd` has moved the leg along the given
2-isomorphism — so `CategoryTheory.Bicategory.isTwoFibreProduct_paste` (**Stacks 003Q**) and
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct` (**Stacks 04SW**)
give the comparison, and
`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct` (**Stacks 04SD**) gives
the two cartesian squares. -/
theorem exists_comparison_chartFibre_fibreBaseChange
    (θ : rr.hom ≫ c.hom ≅ ρρ.hom ≫ g'.hom) :
    ∃ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hG : IsAlgebraicSpace B S hS G)
      (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hH : IsAlgebraicSpace B S hS H)
      (ξ : G ⟶ P) (πG : G ⟶ Tv) (η : H ⟶ Fsp) (πH : H ⟶ Tv) (m : H ⟶ G), IsIso m ∧
      IsPullback ξ πG
          (chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f 𝒲 c Wv eW P eP)
          (representingMap B S hS 𝒯₀.val 𝒲.val Tv Wv eT eW rr.hom) ∧
      IsPullback η πH
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g').pt.val
            𝒦.val Fsp Kv eFib eK (twoFibreProductSquareAlgebraicStacks B S hS f g').snd.hom)
          (representingMap B S hS 𝒯₀.val 𝒦.val Tv Kv eT eK ρρ.hom) ∧
      m ≫ ξ ≫ (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom =
        η ≫ representingMap B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f g').pt.val
          (algebraicSpaceStack.{u, w} B S hS U hU).val Fsp U eFib
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (twoFibreProductSquareAlgebraicStacks B S hS f g').fst.hom := by
  classical
  have hT₀ : IsRepresentableByAlgebraicSpace B S hS 𝒯₀.val := ⟨Tv, hTv, ⟨eT⟩⟩
  -- the chart side: the square of `U ×_𝒳 𝒲` and the inner square over `𝒯₀`
  have hSc : Bicategory.IsTwoFibreProduct
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom f.hom).swap) :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        c.hom f.hom)
  have hTc := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom f.hom).swap.snd rr.hom
  obtain ⟨G, hG, ⟨eG⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          c.hom f.hom).swap.snd rr.hom).pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒲.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom f.hom).swap.pt
      𝒯₀.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom f.hom).swap.snd.hom
      rr.hom.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒲.property hT₀ rr.hom)
      ⟨P, hP, ⟨eP⟩⟩
  -- the fibre side: the square of `U ×_𝒳 𝒦` and the inner square over `𝒯₀`
  have hSf := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    f.hom g'.hom
  have hTf := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g'.hom).snd ρρ.hom
  obtain ⟨H, hH, ⟨eH⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom g'.hom).snd ρρ.hom).pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒦.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g'.hom).pt
      𝒯₀.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g'.hom).snd.hom
      ρρ.hom.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒦.property hT₀ ρρ.hom)
      ⟨Fsp, hFsp, ⟨eFib⟩⟩
  -- the comparison of the two pasted rectangles
  obtain ⟨m, hm, hmfst, -⟩ := exists_isIso_representingMap_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_paste hSf hTf)
    (Bicategory.isTwoFibreProduct_reindexSnd θ (Bicategory.isTwoFibreProduct_paste hSc hTc))
    H G U Tv eH eG (StacksRepresentableCFG.EquivalenceOver.refl _) eT
  refine ⟨G, hG, H, hH, _, _, _, _, m, hm,
    isPullback_representingMap_of_isTwoFibreProduct B S hS hTc P Tv Wv G G eP eT eW eG eG,
    isPullback_representingMap_of_isTwoFibreProduct B S hS hTf Fsp Tv Kv H H eFib eT eK eH eH,
    ?_⟩
  refine Eq.trans (congrArg (fun x => m ≫ x) ?_) (hmfst.trans ?_)
  · exact (representingMap_comp B S hS G P U eG eP
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          c.hom f.hom).swap.snd rr.hom).fst
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom f.hom).swap.fst).symm
  · exact representingMap_comp B S hS H Fsp U eH eFib
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom g'.hom).snd ρρ.hom).fst
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g'.hom).fst

end Comparison

/-! ### Moving the fibre hypothesis along an isomorphism -/

/-- **The fibre hypothesis of Stacks 06LW along an isomorphism, with the morphism to the ambient
space named separately.** This is
`AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt` at an
isomorphism — which is flat, by `AlgebraicGeometry.Space.isFlatAt_of_isIso` — with the composite
`mm ≫ q` presented under another name `q'`, the two being equal by hypothesis. Both uses in this
file come with such a presentation. -/
theorem forall_isRegular_etaleLocalRingMap_germ_of_isIso_of_eq
    {A A' Xs : AlgebraicSpaces B S hS} (mm : A'.1 ⟶ A.1) [IsIso mm] (q : A.1 ⟶ Xs.1)
    (q' : A'.1 ⟶ Xs.1)
    (fs : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS Xs)).sections)
    (zz : Space.GeometricPoint B S hS A'.1) (heq : q' = mm ≫ q)
    (h : ∀ N : Space.SmallEtaleNeighborhood (Space.geometricPointMap q' zz),
        RingTheory.Sequence.IsRegular (Space.etaleLocalRing B S hS A'.1 zz)
          (List.ofFn fun i : Fin r => Space.etaleLocalRingMap A'.2 q' zz
            (Space.etaleLocalRingGerm B S hS Xs.1 (Space.geometricPointMap q' zz) (op N)
              ((fs i).eval (op N.chart))))) :
    ∀ N : Space.SmallEtaleNeighborhood
        (Space.geometricPointMap q (Space.geometricPointMap mm zz)),
      RingTheory.Sequence.IsRegular
          (Space.etaleLocalRing B S hS A.1 (Space.geometricPointMap mm zz))
        (List.ofFn fun i : Fin r => Space.etaleLocalRingMap A.2 q
          (Space.geometricPointMap mm zz)
          (Space.etaleLocalRingGerm B S hS Xs.1
            (Space.geometricPointMap q (Space.geometricPointMap mm zz)) (op N)
            ((fs i).eval (op N.chart)))) := by
  refine (Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt B S hS
    (ObjectProperty.homMk (X := A) (Y := Xs) q) fs mm zz
    (Space.isFlatAt_of_isIso B S hS mm zz.image)).1 ?_
  exact (iff_of_eq (congrArg (fun mm' : A'.1 ⟶ Xs.1 =>
    ∀ N : Space.SmallEtaleNeighborhood (Space.geometricPointMap mm' zz),
      RingTheory.Sequence.IsRegular (Space.etaleLocalRing B S hS A'.1 zz)
        (List.ofFn fun i : Fin r => Space.etaleLocalRingMap A'.2 mm' zz
          (Space.etaleLocalRingGerm B S hS Xs.1 (Space.geometricPointMap mm' zz) (op N)
            ((fs i).eval (op N.chart))))) heq)).1 h

/-! ### The comparison of the two fibres -/

include hU hFsp hP in
/-- **The fibre of the chart base change over a lifted field-valued point, with the regular
sequence transported into it.** Let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space to an
algebraic stack over `S`, let `g : Spec k ⟶ 𝒳` be a field-valued point, let `Fsp` represent the
fibre `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`, let `f₁, …, f_r` be global regular functions
on `U` and let `z` be a geometric point of `F` at which the `f_i` map to a regular sequence in
`𝒪_{F, z̄}`. Let `c : 𝒲 ⟶ 𝒳` be a **surjective** 1-morphism, with `𝒲` represented by the algebraic
space `Wv` and `U ×_𝒳 𝒲` by the algebraic space `P`.

Then there is a field `k'` whose spectrum lies in the site, a field-valued point
`t : Spec k' ⟶ Wv` of the chart, an algebraic space `G` with a cartesian square exhibiting it as
the fibre `P ×_{Wv} Spec k'`, and a geometric point `zG` of `G` such that

* `zG` lies over `p(z)` in `|U|`, and
* the pulled-back functions `g^*f₁, …, g^*f_r` on `P` map to a regular sequence in `𝒪_{G, z̄_G}`.

These are exactly the hypotheses of the flatness half of **Stacks 06LW** for the flat, locally
finitely presented morphism `P ⟶ Wv`. No smoothness of `c` is used, only surjectivity. -/
theorem exists_chartFibre_isPullback_isRegular
    (hcsurj : IsSurjective B S hS c)
    (z : Space.GeometricPoint B S hS Fsp)
    (hreg : FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z) :
    ∃ (k' : Type u) (_ : Field k') (hk' : B.Contains (Spec (.of k')))
      (b' : Spec (.of k') ⟶ S)
      (t : yoneda.obj (fieldPointObject B S hS k' hk' b') ⟶ Wv)
      (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
      (ξ : G ⟶ P) (π' : G ⟶ yoneda.obj (fieldPointObject B S hS k' hk' b'))
      (zG : Space.GeometricPoint B S hS G),
      IsPullback ξ π'
          (chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f 𝒲 c Wv eW P eP) t ∧
        Space.pointsMap B S hS G
            (ξ ≫ (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom) zG.image =
          Space.pointsMap B S hS Fsp
            (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∧
        ∀ N : Space.SmallEtaleNeighborhood (Space.geometricPointMap ξ zG),
          RingTheory.Sequence.IsRegular (Space.etaleLocalRing B S hS G zG)
            (List.ofFn fun i : Fin r => Space.etaleLocalRingMap hG ξ zG
              (Space.etaleLocalRingGerm B S hS P (Space.geometricPointMap ξ zG) (op N)
                ((chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f 𝒲 c P hP eP i).eval
                  (op N.chart)))) := by
  classical
  -- the field-valued point of `𝒳` which `g` is the 1-morphism of, and the 2-isomorphism
  have θg := twoIso_fieldValuedPointStackMorphism_fieldValuedPointMap.{u, w} B S hS 𝒳
    (fieldPointObject B S hS k hk toBase) k (Iso.refl _) g
  -- its lift through the surjective `c`
  obtain ⟨rpt, ρ, ⟨θr⟩⟩ := exists_fieldValuedPoint_lift_of_isSurjective.{u, w} B S hS 𝒳 𝒲 c hcsurj
    (fieldValuedPointMap B S hS
      (schemeFibredCategory B S hS (fieldPointObject B S hS k hk toBase)).val g.hom.hom
      (tautologicalFieldValuedPoint B S hS (fieldPointObject B S hS k hk toBase) k (Iso.refl _)))
  -- the enlargement of the residue field of `z` at which the lift becomes available
  obtain ⟨z₁, c₀, tt, -, hfac, himg, w, hw⟩ :=
    exists_geometricPoint_lift_fieldSpectrum B S hS hk toBase rpt.base
      ⟨rpt.carrier, rpt.field, ⟨rpt.isSpec⟩⟩ ρ
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      z.image
  -- the two readings of the lifted field-valued point as a 1-morphism to `𝒳` agree
  have hρ'' : schemeStackMap.{u, w} B S hS tt ≫ schemeStackMap.{u, w} B S hS ρ =
      schemeStackMap.{u, w} B S hS c₀ :=
    (schemeStackMap_comp.{u, w} B S hS tt ρ).trans
      (congrArg (schemeStackMap.{u, w} B S hS) hfac)
  have θ : (schemeStackMap.{u, w} B S hS tt ≫
        fieldValuedPointStackMorphism.{u, w} B S hS 𝒲 rpt).hom ≫ c.hom ≅
      (schemeStackMap.{u, w} B S hS c₀).hom ≫ g.hom :=
    (α_ (schemeStackMap.{u, w} B S hS tt).hom
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒲 rpt).hom c.hom) ≪≫
      whiskerLeftIso (schemeStackMap.{u, w} B S hS tt).hom θr ≪≫
      (α_ (schemeStackMap.{u, w} B S hS tt).hom (schemeStackMap.{u, w} B S hS ρ).hom
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 _).hom).symm ≪≫
      whiskerRightIso (eqToIso (congrArg (fun m : schemeStack.{u, w} B S hS
        z₁.val.siteObject ⟶ schemeStack.{u, w} B S hS
          (fieldPointObject B S hS k hk toBase) => m.hom) hρ'')) _ ≪≫
      whiskerLeftIso (schemeStackMap.{u, w} B S hS c₀).hom θg
  -- the two presentations of the fibre over the lifted point, compared
  obtain ⟨G, hG, H, hH, ξ, πG, η, πH, m, hm, hsqG, hsqH, hcompat⟩ :=
    exists_comparison_chartFibre_fibreBaseChange.{u, w} B S hS (𝒳 := 𝒳) (U := U) (hU := hU)
      (f := f) (Fsp := Fsp) (hFsp := hFsp) (𝒲 := 𝒲) (c := c) (Wv := Wv) (eW := eW)
      (P := P) (hP := hP) (eP := eP)
      (𝒦 := schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase))
      (𝒯₀ := schemeStack.{u, w} B S hS z₁.val.siteObject) (g' := g)
      (rr := schemeStackMap.{u, w} B S hS tt ≫ fieldValuedPointStackMorphism.{u, w} B S hS 𝒲 rpt)
      (ρρ := schemeStackMap.{u, w} B S hS c₀)
      (Kv := yoneda.obj (fieldPointObject B S hS k hk toBase))
      (Tv := yoneda.obj z₁.val.siteObject)
      (hTv := isAlgebraicSpace_yoneda B S hS _)
      (eK := PresheafOfCategories.sliceElementsEquivalenceOver _)
      (eT := PresheafOfCategories.sliceElementsEquivalenceOver _)
      (eFib := eF) (θ := θ)
  -- the base change of the fibre along the field extension, and the comparison with `H`
  have hF' : IsAlgebraicSpace B S hS (pullback
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀)) :=
    isAlgebraicSpace_pullback B S hS _ (yoneda.map c₀) hFsp
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
  have hsqH' : IsPullback η πH
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀) :=
    (iff_of_eq (congrArg (fun x => IsPullback η πH
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF) x)
      (representingMap_schemeStackMap.{u, w} B S hS c₀))).1 hsqH
  have hj := IsPullback.isoIsPullback_hom_fst _ _ hsqH'
    (IsPullback.of_hasPullback
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF) (yoneda.map c₀))
  -- the regularity hypothesis moves to the enlarged geometric point of the fibre
  obtain ⟨rz, ⟨dz, hdz⟩, ⟨dz₁, hdz₁⟩⟩ :=
    Space.GeometricPoint.exists_common_extension z z₁ rfl himg
  have hdom := fun {x y} d hd => Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates
    B S hS (ObjectProperty.homMk (X := (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)) (Y := ⟨U, hU⟩)
      (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)) a (x := x) (y := y) d hd
  have hregz₁ := (hdom dz₁ hdz₁).2 ((hdom dz hdz).1 hreg)
  -- the projection of the base change along the field extension is flat
  have _ := Space.isFlat_isStableUnderBaseChange B S hS
  have hflatfst : Space.IsFlat B S hS (pullback.fst
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A A' : AlgebraicSpaces B S hS⦄ (mm : A ⟶ A') => Space.IsFlat B S hS mm.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk (X := (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS))
          (Y := (schemeSpace (fieldPointObject B S hS k hk toBase) : AlgebraicSpaces B S hS))
          (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF))
        (ObjectProperty.homMk (X := (schemeSpace z₁.val.siteObject : AlgebraicSpaces B S hS))
          (Y := (schemeSpace (fieldPointObject B S hS k hk toBase) : AlgebraicSpaces B S hS))
          (yoneda.map c₀))).flip
      (Space.isFlat_yoneda_map B S hS c₀
        (flat_of_isField_stalk _ fun _ => isField_stalk_Spec_field k _))
  -- the regularity hypothesis moves to the base change, and then to `H` and to `G`
  have hdomzz : Space.FieldValuedPoint.Dominates B S hS Fsp
      (Space.geometricPointMap (pullback.fst
        (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
        (yoneda.map c₀)) w).val z₁.val := by
    rw [hw]
    exact Space.FieldValuedPoint.dominates_refl B S hS Fsp z₁.val
  obtain ⟨dzz, hdzz⟩ := hdomzz
  have hregF' := (Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt B S hS
      (ObjectProperty.homMk (X := (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)) (Y := ⟨U, hU⟩)
        (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)) a
      (Fs' := ⟨pullback (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
        (yoneda.map c₀), hF'⟩)
      (pullback.fst (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
        (yoneda.map c₀)) w
      ((Space.isFlat_iff_forall_isFlatAt B S hS _).1 hflatfst _)).2
    ((hdom dzz hdzz).1 hregz₁)
  -- the comparison of `H` with that base change, as a named isomorphism
  obtain ⟨jj, hjj⟩ : ∃ jj : H ≅ pullback
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF) (yoneda.map c₀),
      jj.hom ≫ pullback.fst
        (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
        (yoneda.map c₀) = η :=
    ⟨hsqH'.isoIsPullback _ _ (IsPullback.of_hasPullback _ _), hj⟩
  have hinvη : jj.inv ≫ η = pullback.fst
      (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀) := by
    rw [← hjj, Iso.inv_hom_id_assoc]
  have := hm
  -- the regularity hypothesis on `H`, and then on `G`
  have hregH := forall_isRegular_etaleLocalRingMap_germ_of_isIso_of_eq B S hS
    (A := (⟨H, hH⟩ : AlgebraicSpaces B S hS))
    (A' := (⟨pullback (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀), hF'⟩ : AlgebraicSpaces B S hS))
    (Xs := (⟨U, hU⟩ : AlgebraicSpaces B S hS)) jj.inv
    (η ≫ fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)
    (pullback.fst (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (yoneda.map c₀) ≫ fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)
    a w (by rw [← Category.assoc, hinvη]) hregF'
  have hregG := forall_isRegular_etaleLocalRingMap_germ_of_isIso_of_eq B S hS
    (A := (⟨G, hG⟩ : AlgebraicSpaces B S hS)) (A' := (⟨H, hH⟩ : AlgebraicSpaces B S hS))
    (Xs := (⟨U, hU⟩ : AlgebraicSpaces B S hS)) m
    (ξ ≫ (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom)
    (η ≫ fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) a
    (Space.geometricPointMap jj.inv w) hcompat.symm hregH
  refine ⟨z₁.val.carrier, z₁.val.field, z₁.val.contained, z₁.val.toBase, _, G, hG, ξ, πG,
    Space.geometricPointMap m (Space.geometricPointMap jj.inv w), hsqG, ?_, ?_⟩
  · -- the marked point of `G` lies over `p(z)` in `|U|`
    have hfin : Space.pointsMap B S hS H η (Space.geometricPointMap jj.inv w).image =
        z.image :=
      ((Space.pointsMap_comp_apply B S hS jj.inv η w.image).symm.trans
        (congrArg (fun mm : pullback
            (fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF)
            (yoneda.map c₀) ⟶ Fsp =>
          Space.pointsMap B S hS _ mm w.image) hinvη)).trans
        (((Space.geometricPointMap_image _ w).symm.trans
          (congrArg Space.GeometricPoint.image hw)).trans himg)
    refine Eq.trans ?_ (congrArg (Space.pointsMap B S hS Fsp
      (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)) hfin)
    refine Eq.trans (Space.pointsMap_comp_apply B S hS m
      (ξ ≫ (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom)
      (Space.geometricPointMap jj.inv w).image).symm ?_
    refine Eq.trans (congrArg (fun mm => Space.pointsMap B S hS H mm
      (Space.geometricPointMap jj.inv w).image) hcompat) ?_
    exact Space.pointsMap_comp_apply B S hS η
      (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (Space.geometricPointMap jj.inv w).image
  · -- the germs of the pulled-back functions
    intro N
    obtain ⟨N₀⟩ := Space.nonempty_smallEtaleNeighborhood hU
      (Space.geometricPointMap (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom
        (Space.geometricPointMap ξ (Space.geometricPointMap m
          (Space.geometricPointMap jj.inv w))))
    refine (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular
      (Space.etaleLocalRing B S hS G
        (Space.geometricPointMap m (Space.geometricPointMap jj.inv w)))) ?_)).1 (hregG N₀)
    refine congrArg List.ofFn (funext fun i => ?_)
    refine Eq.trans ?_ (congrArg (Space.etaleLocalRingMap hG ξ
      (Space.geometricPointMap m (Space.geometricPointMap jj.inv w)))
      (Space.etaleLocalRingGerm_globalFunctionsMap B S hS
        (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP) (a i)
        (Space.geometricPointMap ξ (Space.geometricPointMap m
          (Space.geometricPointMap jj.inv w))) N N₀)).symm
    exact (RingHom.congr_fun (Space.etaleLocalRingMap_comp hG hP ξ
      (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP).hom
      (Space.geometricPointMap m (Space.geometricPointMap jj.inv w))) _).symm

end AlgebraicGeometry.Stack

end
