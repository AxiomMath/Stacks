module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralOfSmoothChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.NormalizationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmallUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationQuotientMapSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct

/-!
# The normalization of an algebraic stack (Stacks 0GMJ)

Let `𝒳` be an algebraic stack over `S` satisfying the equivalent conditions of Stacks 0GMI, and let
`ν : 𝒳^ν ⟶ 𝒳` be its normalization (Stacks 0GMK,
`AlgebraicGeometry.Stack.AlgebraicStacks.normalization`): for the chosen presentation
`𝒳 ≃ [U/R]`, `𝒳^ν = [U^ν/R^ν]` and `ν` is induced by the morphism of groupoids
`(U^ν, R^ν) ⟶ (U, R)`. Stacks 0GMJ says that `ν` is integral and that for every scheme `T` and
smooth morphism `T ⟶ 𝒳` the fibre product `𝒳^ν ×_𝒳 T` is the normalization of `T`.

## Main results

All in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:

* `isIntegralHom_normalization`: `ν` is integral (Stacks 0CHU).
* `exists_iso_normalizationData_of_isTwoFibreProduct`: for any 1-morphism `ν` whose base change
  along one smooth surjective chart is the normalization of the chart, every base change along a
  smooth 1-morphism from an algebraic space is the normalization of that space.
* `isIntegralHom_normalization_and_isTwoFibreProduct_normSpace` and
  `exists_isIntegralHom_and_isTwoFibreProduct_normSpace`: **Stacks 0GMJ**, about the
  normalization of Stacks 0GMK and in the existential form.

## Implementation notes

The base change of `ν` along the presenting chart `𝒮_U ⟶ 𝒳` is `U^ν ⟶ U`: this is Stacks 04ZN,
`AlgebraicGeometry.Stack.isTwoFibreProduct_presentationQuotientMapSquare`, at the cartesian
source square `R^ν = R ×_{s, U} U^ν` of the normalized groupoid. Integrality of `ν` follows by
Stacks 04ZP and Stacks 06TY, since `U^ν ⟶ U` is integral (Stacks 0BB4).

For an arbitrary smooth `f : T ⟶ 𝒳` the source omits the verification. With `V = U ×_𝒳 T`, the
two pastings

```
(U^ν ×_U V) ⟶ 𝒮_{U^ν} ⟶ 𝒳^ν        (𝒳^ν ×_𝒳 T) ×_T V ⟶ 𝒳^ν ×_𝒳 T ⟶ 𝒳^ν
     |            |       |                |                   |          |
     v            v       v                v                   v          v
     V    ⟶     𝒮_U   ⟶  𝒳                V        ⟶          T    ⟶   𝒳
```

are 2-fibre products of the same cospan up to the 2-cell of `V`, so their apexes are equivalent
over `V`. The first is `U^ν ×_U V = V^ν` by Stacks 07U4, part (4), since `V ⟶ U` is a base change
of `f`, hence smooth. So the base change of `𝒳^ν ×_𝒳 T ⟶ T` along the smooth surjective `V ⟶ T`
is the normalization of `V`, and the normalization descends
(`AlgebraicGeometry.Space.NormalizationData.exists_iso_of_isPullback_of_isSmooth`).

## References

* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06TY](https://stacks.math.columbia.edu/tag/06TY)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0CHU](https://stacks.math.columbia.edu/tag/0CHU)
* [Stacks Project, Tag 0GMI](https://stacks.math.columbia.edu/tag/0GMI)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
* [Stacks Project, Tag 0GMK](https://stacks.math.columbia.edu/tag/0GMK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Presentation

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)

/-- The chart `𝒮_U ⟶ 𝒳` of a presentation is smooth (Stacks 04X0). -/
theorem isSmooth_presentationObjectMorphismAlgebraicStacks :
    AlgebraicStacks.IsSmooth B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) := by
  obtain ⟨hrep, hrel⟩ := GroupoidPresentation.isRelativelySmooth_atlasMap P 𝒳.property
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hrel

/-- The chart `𝒮_U ⟶ 𝒳` of a presentation is surjective (Stacks 04X0). -/
theorem isSurjective_presentationObjectMorphismAlgebraicStacks :
    IsSurjective B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
    (presentationObjectMorphismAlgebraicStacks B S hS P)
    (GroupoidPresentation.isRepresentableByAlgebraicSpaces_atlasMap P 𝒳.property)).mpr
    (GroupoidPresentation.isRelativelySurjective_atlasMap P 𝒳.property)

end Presentation

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
    (fun X : Scheme.{u} =>
      ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳)

/-- The normalization is the 1-morphism `AlgebraicGeometry.Stack.presentationQuotientMap` of its
normalized groupoid into the presenting groupoid. -/
theorem normalization_eq_presentationQuotientMap :
    normalization 𝒳 h𝒳 = presentationQuotientMap B S hS (normalizationPresentation 𝒳)
      (normalizationGroupoidOf 𝒳 h𝒳).smooth (normalizationGroupoidOf 𝒳 h𝒳).hom :=
  rfl

/-- **The base change of the normalization along the presenting chart**: the square of Stacks 04ZN
for the normalized groupoid, a 2-fibre product with apex `𝒮_{U^ν}`. -/
noncomputable def normalizationChartSquare :
    Bicategory.TwoCommSq (normalization 𝒳 h𝒳)
      (presentationObjectMorphismAlgebraicStacks B S hS (normalizationPresentation 𝒳)) :=
  presentationQuotientMapSquare B S hS (normalizationPresentation 𝒳)
    (normalizationGroupoidOf 𝒳 h𝒳).smooth (normalizationGroupoidOf 𝒳 h𝒳).hom

/-- **Stacks 04ZN for the normalized groupoid**: the base change of the normalization along the
presenting chart `𝒮_U ⟶ 𝒳` is `𝒮_{U^ν} ⟶ 𝒮_U`. -/
noncomputable def isTwoFibreProduct_normalizationChartSquare :
    Bicategory.IsTwoFibreProduct (normalizationChartSquare 𝒳 h𝒳) :=
  isTwoFibreProduct_presentationQuotientMapSquare B S hS (normalizationPresentation 𝒳)
    (normalizationGroupoidOf 𝒳 h𝒳).smooth (normalizationGroupoidOf 𝒳 h𝒳).hom
    (normalizationGroupoidOf 𝒳 h𝒳).isPullback_source

/-- **The normalization of an algebraic stack is integral** (Stacks 0CHU, part (1)): it is
representable by algebraic spaces and integral in the sense of Stacks 04XB. Its base change
along the smooth surjective presenting chart is the normalization morphism `U^ν ⟶ U`, which is
integral by Stacks 0BB4, part (2). -/
theorem isIntegralHom_normalization :
    AlgebraicStacks.IsIntegralHom B S hS (normalization 𝒳 h𝒳) :=
  isIntegralHom_of_isTwoFibreProduct_smoothChart B S hS (normalization 𝒳 h𝒳)
    (normalizationPresentation 𝒳).groupoid.objects.property
    (normalizationGroupoidOf 𝒳 h𝒳).data.isAlgebraicSpace
    (presentationObjectMorphismAlgebraicStacks B S hS (normalizationPresentation 𝒳))
    (normalizationGroupoidOf 𝒳 h𝒳).data.hom (normalizationChartSquare 𝒳 h𝒳).fst
    (normalizationChartSquare 𝒳 h𝒳).swap.iso
    (isSurjective_presentationObjectMorphismAlgebraicStacks _)
    (isSmooth_presentationObjectMorphismAlgebraicStacks _)
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_normalizationChartSquare 𝒳 h𝒳))
    ((normalizationGroupoidOf 𝒳 h𝒳).data.isIntegralHom_hom
      (normalizationPresentation 𝒳).groupoid.objects.property)

section SmoothChart

variable {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (ν : 𝒳' ⟶ 𝒳)
  {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
  (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒳)
  (DW : Space.NormalizationData B S hS W)
  (a : algebraicSpaceStack.{u, w} B S hS DW.space DW.isAlgebraicSpace ⟶ 𝒳')
  (θ : (Bicategory.InducedBicategory.mkHom (associatedMap B S hS DW.hom).1 :
      algebraicSpaceStack.{u, w} B S hS DW.space DW.isAlgebraicSpace ⟶
        algebraicSpaceStack.{u, w} B S hS W hW) ≫ g ≅ a ≫ ν)

/-- **The base change of `ν` along a smooth 1-morphism is the normalization.** Suppose the base
change of `ν : 𝒳' ⟶ 𝒳` along a surjective smooth `g : W ⟶ 𝒳` from an algebraic space is the
normalization `W^ν ⟶ W`. Let `f : 𝒯 ⟶ 𝒳` be a smooth 1-morphism from a category represented by
an algebraic space `T`, with normalization data `D`, and let `P` be a 2-fibre product of `(f, ν)`
represented by an algebraic space `V'`. Then `V'` is the normalization of `T`: the projection
`V' ⟶ T` is isomorphic over `T` to `D.space ⟶ T`. -/
theorem exists_iso_normalizationData_of_isTwoFibreProduct
    (hgS : IsSurjective B S hS g) (hgSm : AlgebraicStacks.IsSmooth B S hS g)
    (hWfin : Space.HasLocallyFiniteIrreducibleComponents B S hS W)
    (hQ₀ : Bicategory.IsTwoFibreProduct
      (smoothChartSquare B S hS ν hW DW.isAlgebraicSpace g DW.hom a θ))
    {𝒯 : AlgebraicStacks.{u, w} B S hS} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T)
    (eT : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (D : Space.NormalizationData B S hS T)
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsSmooth B S hS f)
    (P : Bicategory.TwoCommSq f ν) (hP : Bicategory.IsTwoFibreProduct P)
    {V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV' : IsAlgebraicSpace B S hS V')
    (eV' : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
      (presheafOfCategories (V' ⋙ typeToCat)).p) :
    ∃ e : V' ≅ D.space,
      e.hom ≫ D.hom = representingMap B S hS P.pt.val 𝒯.val V' T eV' eT P.fst.hom := by
  have h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val := ⟨T, hT, ⟨eT⟩⟩
  have hrel : ∀ {𝒴 : AlgebraicStacks.{u, w} B S hS} (k : 𝒴 ⟶ 𝒳),
      IsRepresentableByAlgebraicSpace B S hS 𝒴.val → AlgebraicStacks.IsSmooth B S hS k →
        IsRelativelySmooth B S hS k.hom := fun {𝒴} k h𝒴 hk =>
    have hkrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒴 k.hom
    ⟨hkrep, (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      𝒴.property 𝒳.property k.hom hkrep).1 hk⟩
  have hfrel := hrel f h𝒯 hf
  have hgrel := hrel g (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW) hgSm
  have hgrep := hgrel.1
  -- 2-fibre products of algebraic stacks, with representable apex
  have key : ∀ {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS} (k : 𝒞 ⟶ ℬ) (l : 𝒜 ⟶ ℬ),
      IsRepresentableByAlgebraicSpace B S hS 𝒜.val →
        IsRepresentableByAlgebraicSpace B S hS 𝒞.val →
        Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS k l) ×'
          Bicategory.IsTwoFibreProduct
            (twoFibreProductSquareAlgebraicStacks B S hS k l).underlying ×'
          IsRepresentableByAlgebraicSpace B S hS
            (twoFibreProductSquareAlgebraicStacks B S hS k l).pt.val :=
    fun {_ ℬ _} k l h𝒜 h𝒞 =>
    have hX := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k l
    have hXu := isTwoFibreProduct_underlying_algebraicStacks B S hS _ hX
    ⟨hX, hXu, isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS _ _ _
      l.hom k.hom _ hXu
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS ℬ.property h𝒜 l.hom) h𝒞⟩
  -- the 2-fibre product `V = W ×_𝒳 𝒯`
  let Q := twoFibreProductSquareAlgebraicStacks B S hS g f
  obtain ⟨hQ, hQu, hQrep⟩ := key g f h𝒯
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW)
  obtain ⟨W₂, hW₂, ⟨eW₂⟩⟩ := id hQrep
  -- the two base changes and their representing morphisms
  let u := representingMap B S hS Q.pt.val (algebraicSpaceStack.{u, w} B S hS W hW).val W₂ W eW₂
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst.hom
  let v := representingMap B S hS Q.pt.val 𝒯.val W₂ T eW₂ eT Q.snd.hom
  have hQfst : IsRelativelySmooth B S hS Q.fst.hom :=
    isRelativelySmooth_baseChange.{u, u, u} B S hS _ _ _ f.hom g.hom Q.underlying hQu hfrel
  have hQswap := isTwoFibreProduct_underlying_algebraicStacks B S hS Q.swap
    (Bicategory.isTwoFibreProduct_swap hQ)
  have hQsnd : IsRelativelySmooth B S hS Q.snd.hom :=
    isRelativelySmooth_baseChange.{u, u, u} B S hS _ _ _ g.hom f.hom Q.swap.underlying hQswap
      hgrel
  have hu : Space.IsSmooth B S hS u :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      Q.fst.hom hQfst.1 W₂ W hW₂ hW eW₂ _).1 hQfst.2
  have hv : Space.IsSmooth B S hS v :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      Q.snd.hom hQsnd.1 W₂ T hW₂ hT eW₂ eT).1 hQsnd.2
  have hgsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) g.hom hgrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hgrep).1 hgS
  have hvs : Space.IsSurjective B S hS v :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      Q.snd.hom hQsnd.1 W₂ T hW₂ hT eW₂ eT).1
      (hasRelativeProperty_baseChange.{u, u, u, u} B S hS (Space.surjectiveMorphismProperty B S hS)
        _ _ _ g.hom f.hom Q.swap.underlying hQswap hgrep hgsurj)
  -- the normalization of `W₂`, by Stacks 07U4 (4) along the smooth `u`
  obtain ⟨D', mm, hmm⟩ := DW.exists_isPullback_hom_of_isSmooth hW hW₂ u hu hWfin
  -- `E = W₂ ×_W W^ν` and `F = W₂ ×_T V'`
  let C₀ := smoothChartSquare B S hS ν hW DW.isAlgebraicSpace g DW.hom a θ
  let E := twoFibreProductSquareAlgebraicStacks B S hS Q.fst C₀.fst
  obtain ⟨hE, hEu, hErep⟩ := key Q.fst C₀.fst
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS DW.space DW.isAlgebraicSpace) hQrep
  have hPrep : IsRepresentableByAlgebraicSpace B S hS P.pt.val := ⟨V', hV', ⟨eV'⟩⟩
  let F := twoFibreProductSquareAlgebraicStacks B S hS Q.snd P.fst
  obtain ⟨hF, hFu, hFrep⟩ := key Q.snd P.fst hPrep hQrep
  obtain ⟨RE, hRE, ⟨eE⟩⟩ := hErep
  obtain ⟨RF, hRF, ⟨eF⟩⟩ := hFrep
  have hEpb := isPullback_representingMap_of_isTwoFibreProduct B S hS hEu W₂ DW.space W RE RE
    eW₂ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eE eE
  have hFpb := isPullback_representingMap_of_isTwoFibreProduct B S hS hFu W₂ V' T RF RF
    eW₂ eV' eT eF eF
  have hC₀ : representingMap B S hS
      (algebraicSpaceStack.{u, w} B S hS DW.space DW.isAlgebraicSpace).val
      (algebraicSpaceStack.{u, w} B S hS W hW).val DW.space W
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) C₀.fst.hom = DW.hom :=
    representingMap_associatedMap B S hS DW.space W DW.hom
  have hEpb' : IsPullback (representingMap B S hS E.pt.val Q.pt.val RE W₂ eE eW₂ E.fst.hom)
      (representingMap B S hS E.pt.val
        (algebraicSpaceStack.{u, w} B S hS DW.space DW.isAlgebraicSpace).val RE DW.space eE
        (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd.hom) u DW.hom := by
    rwa [← hC₀]
  -- the two pastings, over the same cospan
  let CE := C₀.pasteFst E
  have hCE : Bicategory.IsTwoFibreProduct CE := Bicategory.isTwoFibreProduct_pasteFst C₀ hQ₀ E hE
  let PF := (P.pasteFst F).reindexFst Q.iso.symm
  have hPF : Bicategory.IsTwoFibreProduct PF :=
    Bicategory.isTwoFibreProduct_reindexFst _ (Bicategory.isTwoFibreProduct_pasteFst P hP F hF)
  let m := Bicategory.twoFibreProductPreHom hPF CE
  let n := Bicategory.twoFibreProductPreHom hCE PF
  obtain ⟨θ₁, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hCE (m.comp n)
    (Bicategory.TwoCommSq.PreHom.id _)
  obtain ⟨θ₂, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hPF (n.comp m)
    (Bicategory.TwoCommSq.PreHom.id _)
  let φ : RE ≅ RF :=
    { hom := representingMap B S hS E.pt.val F.pt.val RE RF eE eF m.hom.hom
      inv := representingMap B S hS F.pt.val E.pt.val RF RE eF eE n.hom.hom
      hom_inv_id :=
        (representingMap_comp B S hS RE RF RE eE eF eE m.hom.hom n.hom.hom).symm.trans
          ((representingMap_congr_twoIso B S hS RE RE eE eE
            (Bicategory.InducedBicategory.isoHom (f := m.hom ≫ n.hom) (g := 𝟙 E.pt) θ₁)).trans
              (representingMap_id B S hS _ RE eE))
      inv_hom_id :=
        (representingMap_comp B S hS RF RE RF eF eE eF n.hom.hom m.hom.hom).symm.trans
          ((representingMap_congr_twoIso B S hS RF RF eF eF
            (Bicategory.InducedBicategory.isoHom (f := n.hom ≫ m.hom) (g := 𝟙 F.pt) θ₂)).trans
              (representingMap_id B S hS _ RF eF)) }
  have hφ : φ.hom ≫ representingMap B S hS F.pt.val Q.pt.val RF W₂ eF eW₂ F.fst.hom =
      representingMap B S hS E.pt.val Q.pt.val RE W₂ eE eW₂ E.fst.hom :=
    (representingMap_comp B S hS RE RF W₂ eE eF eW₂ m.hom.hom F.fst.hom).symm.trans
      (representingMap_congr_twoIso B S hS RE W₂ eE eW₂
        (Bicategory.InducedBicategory.isoHom m.isoFst)).symm
  let ψ : D'.space ≅ RE := hmm.flip.isoIsPullback _ _ hEpb'
  have hψ : ψ.hom ≫ representingMap B S hS E.pt.val Q.pt.val RE W₂ eE eW₂ E.fst.hom = D'.hom :=
    hmm.flip.isoIsPullback_hom_fst _ _ hEpb'
  have hD : (ψ ≪≫ φ).hom ≫
      representingMap B S hS F.pt.val Q.pt.val RF W₂ eF eW₂ F.fst.hom = D'.hom := by
    rw [Iso.trans_hom, Category.assoc, hφ, hψ]
  have hsq : IsPullback ((ψ ≪≫ φ).hom ≫
      representingMap B S hS F.pt.val P.pt.val RF V' eF eV' F.snd.hom) D'.hom
      (representingMap B S hS P.pt.val 𝒯.val V' T eV' eT P.fst.hom) v :=
    IsPullback.of_iso hFpb.flip (ψ ≪≫ φ).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
      ((Category.comp_id _).trans (by rw [← hD, Iso.symm_hom, Iso.inv_hom_id_assoc]; rfl))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact D.exists_iso_of_isPullback_of_isSmooth hT hV' hW₂ _ v hv hvs D' _ hsq

end SmoothChart

/-- The normalization data of the algebraic space represented by an object of the site whose
quasi-compact opens have finitely many irreducible components: its normalization morphism is
`AlgebraicGeometry.Space.normSpaceProj`. -/
theorem ofRepresentable_hom_eq_normSpaceProj (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    (Space.NormalizationData.ofRepresentable B S hS U hU
        (Space.contains_normalizationScheme B S hS U hU)).hom =
      yoneda.map (Space.normSpaceProj B S hS U hU) := by
  refine congrArg yoneda.map ((BigFppfOver.toScheme B S hS).map_injective ?_)
  exact (Exists.choose_spec (BigFppfOver.exists_hom_of_comp_eq B S hS _ rfl)).trans
    (Space.toScheme_map_normSpaceProj B S hS U hU).symm

/-- **Stacks 0GMJ.** Let `𝒳` be an algebraic stack over `S` satisfying the equivalent conditions
of Stacks 0GMI, and let `ν : 𝒳^ν ⟶ 𝒳` be its normalization (Stacks 0GMK). Then `ν` is integral
(Stacks 0CHU), and for every scheme `U` over `S` and every smooth 1-morphism `f : U ⟶ 𝒳`, every
2-fibre product `U ×_𝒳 𝒳^ν` is the normalization of `U`: it is represented by an algebraic space
isomorphic, over `U`, to the normalization `U^ν ⟶ U` of the scheme `U`
(`AlgebraicGeometry.Space.normSpace`, `AlgebraicGeometry.Space.normSpaceProj`; Stacks 035N).

The finiteness of irreducible components of the quasi-compact opens of `U` that the
normalization of `U` needs is condition (2) of Stacks 0GMI for the smooth chart `f`. -/
@[stacks 0GMJ]
theorem isIntegralHom_normalization_and_isTwoFibreProduct_normSpace :
    AlgebraicStacks.IsIntegralHom B S hS (normalization 𝒳 h𝒳) ∧
      ∀ (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
        (hf : AlgebraicStacks.IsSmooth B S hS f)
        (P : Bicategory.TwoCommSq f (normalization 𝒳 h𝒳)) (_ : Bicategory.IsTwoFibreProduct P),
        ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS V)
          (eV : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
            (presheafOfCategories (V ⋙ typeToCat)).p)
          (e : V ≅ yoneda.obj (Space.normSpace B S hS U
            ((exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳 U f hf))),
          e.hom ≫ yoneda.map (Space.normSpaceProj B S hS U
              ((exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳 U f hf)) =
            representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val V (yoneda.obj U) eV
              (PresheafOfCategories.sliceElementsEquivalenceOver U) P.fst.hom := by
  refine ⟨isIntegralHom_normalization 𝒳 h𝒳, fun U f hf P hP => ?_⟩
  set hU := (exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳 U f hf
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    (normalizationStack 𝒳 h𝒳).val 𝒳.val (schemeStack.{u, w} B S hS U).val
    (normalization 𝒳 h𝒳).hom f.hom P.underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS P hP)
    (isIntegralHom_normalization 𝒳 h𝒳).1
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  obtain ⟨e, he⟩ := exists_iso_normalizationData_of_isTwoFibreProduct (normalization 𝒳 h𝒳)
    (normalizationPresentation 𝒳).groupoid.objects.property
    (presentationObjectMorphismAlgebraicStacks B S hS (normalizationPresentation 𝒳))
    (normalizationGroupoidOf 𝒳 h𝒳).data (normalizationChartSquare 𝒳 h𝒳).fst
    (normalizationChartSquare 𝒳 h𝒳).swap.iso
    (isSurjective_presentationObjectMorphismAlgebraicStacks _)
    (isSmooth_presentationObjectMorphismAlgebraicStacks _)
    (hasLocallyFiniteIrreducibleComponents_objects 𝒳 h𝒳 (normalizationPresentation 𝒳))
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_normalizationChartSquare 𝒳 h𝒳))
    (isAlgebraicSpace_yoneda B S hS U) (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (Space.NormalizationData.ofRepresentable B S hS U hU
      (Space.contains_normalizationScheme B S hS U hU))
    f hf P hP hV eV
  refine ⟨V, hV, eV, e, ?_⟩
  rwa [← ofRepresentable_hom_eq_normSpaceProj U hU]

/-- **Stacks 0GMJ, in the existential form the source states.** An algebraic stack `𝒳` over `S`
satisfying the equivalent conditions of Stacks 0GMI admits an integral 1-morphism of algebraic
stacks `𝒳^ν ⟶ 𝒳` such that for every scheme `U` and smooth `U ⟶ 𝒳` every 2-fibre product
`U ×_𝒳 𝒳^ν` is the normalization of `U`. The witness is the normalization of Stacks 0GMK. -/
@[stacks 0GMJ "the existential form"]
theorem exists_isIntegralHom_and_isTwoFibreProduct_normSpace :
    ∃ (𝒳ν : AlgebraicStacks.{u, w} B S hS) (ν : 𝒳ν ⟶ 𝒳),
      AlgebraicStacks.IsIntegralHom B S hS ν ∧
      ∀ (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
        (hf : AlgebraicStacks.IsSmooth B S hS f)
        (P : Bicategory.TwoCommSq f ν) (_ : Bicategory.IsTwoFibreProduct P),
        ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS V)
          (eV : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
            (presheafOfCategories (V ⋙ typeToCat)).p)
          (e : V ≅ yoneda.obj (Space.normSpace B S hS U
            ((exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳 U f hf))),
          e.hom ≫ yoneda.map (Space.normSpaceProj B S hS U
              ((exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳 U f hf)) =
            representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val V (yoneda.obj U) eV
              (PresheafOfCategories.sliceElementsEquivalenceOver U) P.fst.hom :=
  ⟨normalizationStack 𝒳 h𝒳, normalization 𝒳 h𝒳,
    isIntegralHom_normalization_and_isTwoFibreProduct_normSpace 𝒳 h𝒳⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
