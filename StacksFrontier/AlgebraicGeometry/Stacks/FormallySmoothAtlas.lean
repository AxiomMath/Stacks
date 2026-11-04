module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.GluedChartSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange

/-!
# Smooth atlases that are formally smooth on objects

A scheme atlas of an algebraic stack is a 1-morphism `a : (Sch/U)_{fppf} ⟶ 𝒳` which is
representable by algebraic spaces, surjective and smooth (Stacks 026O). Its base changes along
scheme-valued points of `𝒳` are algebraic spaces smooth over the test scheme; that they are
*formally* smooth, and so that `a` is formally smooth on objects in the sense of **Stacks 06D0**,
is the implication of **Stacks 04AM** from smoothness to formal smoothness, for morphisms of
algebraic spaces which need not be representable. That implication is not in this library (it is
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent`).

The proof of **Stacks 06DC** needs exactly this of the atlases of the loci
`ℋ_{d,lci}(𝒳/𝒴)`: composing an atlas with the 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`, it reads formal
smoothness on objects of the composite off Stacks 06D2. This file supplies it without Stacks 04AM
by tracking the property along the constructions that produce the atlases: it holds for the
étale atlas of a category representable by an algebraic space, whose base changes are schemes;
it is preserved by composition (Stacks 06D2) and by base change (Stacks 06D1, here through
**Stacks 06D3** and the base change of relative properties of Stacks 03YK); so it is inherited
along the two constructions of algebraic stacks used upstream, Stacks 05UL and Stacks 05UN.

## Main definitions

* `AlgebraicGeometry.Stack.HasFormallySmoothAtlas`: a scheme atlas which is representable by
  algebraic spaces, surjective, smooth and formally smooth on objects.

## Main results

* `AlgebraicGeometry.Stack.hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpace`: a category
  representable by an algebraic space has one.
* `AlgebraicGeometry.Stack.hasFormallySmoothAtlas_of_smoothPresentation`: Stacks 05UL with the
  property carried along.
* `AlgebraicGeometry.Stack.hasFormallySmoothAtlas_of_isTwoFibreProduct` and
  `AlgebraicGeometry.Stack.hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpaces`: Stacks
  05UN with the property carried along.
* `AlgebraicGeometry.Stack.hasFormallySmoothAtlas_of_onObjects_schemePoint`: a scheme-valued
  point which is limit preserving, formally smooth and surjective on objects is such an atlas.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_formallySmoothAtlas`: a stack
  with representable diagonal receiving a family of 1-morphisms out of categories with such
  atlases, each limit preserving and formally smooth on objects and jointly surjective on
  objects, is an algebraic stack. This is the closing step of Stacks 06DC.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 05UL](https://stacks.math.columbia.edu/tag/05UL)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D2](https://stacks.math.columbia.edu/tag/06D2)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A category fibred in groupoids over the big fppf site of `S` *has a formally smooth atlas*
when it receives a 1-morphism from the big fppf site of an object `U` of the site which is
representable by algebraic spaces, surjective and smooth — a scheme atlas in the sense of
Stacks 026O — and which is moreover formally smooth on objects (Stacks 06D0). -/
def HasFormallySmoothAtlas (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    Prop :=
  ∃ (U : BigFppfOver B S hS) (a : schemeFibredCategory B S hS U ⟶ 𝒳)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom),
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.surjectiveMorphismProperty B S hS)
        a ha ∧
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
        a ha ∧
      IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U) 𝒳 a

/-- **A category representable by an algebraic space has a formally smooth atlas.** The atlas is
the surjective étale scheme atlas of the representing algebraic space, transported along the
equivalence; it is formally étale by Stacks 04AL, hence its base changes are formally smooth
(Stacks 06D3, through `AlgebraicGeometry.Stack.prop_transportedPresentation`). -/
theorem hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    HasFormallySmoothAtlas B S hS 𝒳 := by
  obtain ⟨F, hF, ⟨e⟩⟩ := id h𝒳
  obtain ⟨U, atl, hsurjp, hetalep⟩ := hF.exists_atlas
  have hsurj : Space.IsSurjective B S hS atl :=
    (Space.surjective_iff_surjective_pointsMap B S hS F hF U atl).1 hsurjp
  have hsmooth : Space.IsSmooth B S hS atl :=
    Space.isSmooth_of_isEtale B S hS hF ((Space.isEtale_iff_presheaf_of_yoneda B S hS atl).2
      hetalep)
  have hfs : Space.FormallySmooth atl := fun T T' hT hT' i hi z w hzw =>
    let ⟨v, hv⟩ := Space.formallyEtale_of_etale B S hS atl hetalep T T' hT hT' i hi z w hzw
    ⟨v, hv.1⟩
  let a : schemeFibredCategory B S hS U ⟶ 𝒳 := InducedBicategory.mkHom
    (BasedFunctor.comp (presentationBasedFunctor B S hS U atl) ⟨e.inv.functor, e.inv.w⟩)
  have ha : IsRepresentableByAlgebraicSpaces B S hS a.hom :=
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳 U _
  have key := fun (P : MorphismProperty (AlgebraicSpaces B S hS))
      [P.IsStableUnderBaseChange] hP => prop_transportedPresentation B S hS P hF e U atl hP
  exact ⟨U, a, ha, key (Space.surjectiveMorphismProperty B S hS) hsurj,
    key (Space.smoothMorphismProperty B S hS) hsmooth,
    BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS a ha
      (key (Space.formallySmoothProperty B S hS) hfs)⟩

/-- **Stacks 05UL with a formally smooth atlas.** If `v : 𝒰 ⟶ 𝒳` is representable by algebraic
spaces, surjective, smooth and formally smooth on objects, and `𝒰` is representable by an
algebraic space, then `𝒳` has a formally smooth atlas: the formally smooth atlas of `𝒰` followed
by `v`, by Stacks 0301, Stacks 045B and Stacks 06D2. -/
theorem hasFormallySmoothAtlas_of_smoothPresentation
    {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (v : 𝒰 ⟶ 𝒳)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) v hv)
    (hfs : IsFormallySmoothOnObjects B S hS 𝒰 𝒳 v) :
    HasFormallySmoothAtlas B S hS 𝒳 := by
  obtain ⟨U, g, hg, hgsurj, hgsmooth, hgfs⟩ :=
    hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpace B S hS 𝒰 h𝒰
  exact ⟨U, g ≫ v, isRepresentableByAlgebraicSpaces_comp B S hS g v hg hv,
    hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) g v hg hv hgsurj hsurj,
    hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) g v hg hv hgsmooth hsmooth,
    BigFppfOver.isFormallySmoothOnObjects_comp B S hS _ _ _ g v hgfs hfs⟩

/-- **Formal smoothness on objects of a representable 1-morphism is stable under base change**,
in an arbitrary 2-fibre product square. For representable 1-morphisms formal smoothness on
objects is the relative property of Stacks 03YK at formal smoothness (**Stacks 06D3**), and that
relative property passes to the base change with no hypothesis on the property
(`AlgebraicGeometry.Stack.relativeProperty_baseChange`). -/
theorem isFormallySmoothOnObjects_fst_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (R : TwoCommSq g f) (hR : IsTwoFibreProduct R)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hfs : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 f) :
    IsFormallySmoothOnObjects B S hS R.pt 𝒵 R.fst :=
  BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS R.fst
    (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f g R hR hf)
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.formallySmoothProperty B S hS)
      𝒳 𝒴 𝒵 f g R hR
      (BigFppfOver.isRelativelyFormallySmooth_of_isFormallySmoothOnObjects B S hS f hfs))

/-- **Stacks 05UN along a 2-fibre product, with a formally smooth atlas.** If `a` is a formally
smooth atlas of `𝒴` and `R` is a 2-fibre product of `g : 𝒵 ⟶ 𝒴` and `a` whose apex is
representable by an algebraic space, then `𝒵` has a formally smooth atlas: the projection of
`R` to `𝒵` is a base change of `a`, hence representable by algebraic spaces, surjective and
smooth (Stacks 0302 and Stacks 045C) and formally smooth on objects, and Stacks 05UL applies. -/
theorem hasFormallySmoothAtlas_of_isTwoFibreProduct
    {𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {U : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hasurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) a ha)
    (hasmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) a ha)
    (hafs : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U) 𝒴 a)
    (R : TwoCommSq g a) (hR : IsTwoFibreProduct R)
    (hpt : IsRepresentableByAlgebraicSpace B S hS R.pt) :
    HasFormallySmoothAtlas B S hS 𝒵 :=
  hasFormallySmoothAtlas_of_smoothPresentation B S hS R.fst hpt
    (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ a g R hR ha)
    (hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) _ _ _ a g R hR ha hasurj)
    (hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) _ _ _ a g R hR ha hasmooth)
    (isFormallySmoothOnObjects_fst_of_isTwoFibreProduct B S hS a g R hR ha hafs)

/-- **Stacks 05UN with a formally smooth atlas.** If `j : 𝒳 ⟶ 𝒴` is representable by algebraic
spaces and `𝒴` has a formally smooth atlas, then so does `𝒳`: base change the atlas along `j`;
the apex is representable by an algebraic space by Stacks 0300. -/
theorem hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (h𝒴 : HasFormallySmoothAtlas B S hS 𝒴) :
    HasFormallySmoothAtlas B S hS 𝒳 := by
  obtain ⟨U, a, ha, hasurj, hasmooth, hafs⟩ := h𝒴
  exact hasFormallySmoothAtlas_of_isTwoFibreProduct B S hS a j ha hasurj hasmooth hafs
    (twoFibreSquare a j).swap (isTwoFibreProduct_swap (isTwoFibreSquare a j))
    (isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS j a hj
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))

/-- **A scheme-valued point which is limit preserving, formally smooth and surjective on objects
is a formally smooth atlas**, of a category fibred in groupoids whose diagonal is representable
by algebraic spaces. Representability is Stacks 045G, surjectivity Stacks 06D7, and smoothness
Stacks 04AM from local finite presentation (Stacks 06CX) and formal smoothness (Stacks 06D3);
this is the content of `AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint`
before the assembly. -/
theorem hasFormallySmoothAtlas_of_onObjects_schemePoint
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    (U : BigFppfOver B S hS) (v : schemeFibredCategory B S hS U ⟶ 𝒴)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS U) 𝒴 v)
    (hsmooth : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U) 𝒴 v)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS U).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor v)) :
    HasFormallySmoothAtlas B S hS 𝒴 := by
  have hv : IsRepresentableByAlgebraicSpaces B S hS v.hom :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp hdiag) U v.hom
  have hlfp := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation
    B S hS (schemeFibredCategory B S hS U) 𝒴 v hv).mp hlim
  have hfs := (BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth
    B S hS v hv).mp hsmooth
  exact ⟨U, v, hv,
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS v hv).mp hsurj,
    fun V y hy F hF he =>
      Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth
        (hlfp V y hy F hF he) (hfs V y hy F hF he),
    hsmooth⟩

/-- **A formally smooth atlas is limit preserving on objects**: it is smooth, hence locally of
finite presentation (Stacks 04AJ and Stacks 045F), hence limit preserving on objects by Stacks
06CX. -/
theorem isLimitPreservingOnObjects_of_hasRelativeProperty_smooth
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒳 ⟶ 𝒴)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) a ha) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 a :=
  (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 a ha).mpr
    (hasRelativeProperty_mono.{u, u, u + 1, u + 1, u + 1} B S hS
      (P := Space.smoothMorphismProperty B S hS)
      (P' := Space.locallyOfFinitePresentationProperty B S hS)
      (fun _ _ _ h => Space.isLocallyOfFinitePresentation_of_isSmooth B S hS h) ha hsmooth)

/-- **Joint surjectivity on objects passes to a family of composites.** If each `a i` is
surjective on objects and the family `π` is jointly surjective on objects, then the family of
composites `a i ⋙ π i` is jointly surjective on objects: compose the two field extensions, as
in Stacks 06D6. -/
theorem isJointlySurjectiveOnObjects_comp
    {I : Type*} {X Y : I → Type*} [∀ i, Category (X i)] [∀ i, Category (Y i)]
    {Z : Type*} [Category Z]
    (pX : ∀ i, X i ⥤ BigFppfOver B S hS) (pY : ∀ i, Y i ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS) (a : ∀ i, X i ⥤ Y i) (π : ∀ i, Y i ⥤ Z)
    (hπ : ∀ i, π i ⋙ pZ = pY i)
    (ha : ∀ i, IsSurjectiveOnObjects B S hS (pX i) (pY i) (a i))
    (hsurj : IsJointlySurjectiveOnObjects B S hS pY pZ π) :
    IsJointlySurjectiveOnObjects B S hS pX pZ (fun i => a i ⋙ π i) := by
  intro U hU z hz
  obtain ⟨i, W, hW, g, y, hy, β, hβ⟩ := hsurj U hU z hz
  obtain ⟨V, hV, f, x, hx, α, hα⟩ := ha i W hW y hy
  let : (pY i).IsHomLift f α := hα
  let : pZ.IsHomLift f ((π i).map α) := Functor.isHomLift_map_of_comp_eq (hπ i) f α
  let : pZ.IsHomLift g β := hβ
  exact ⟨i, V, hV, f ≫ g, x, hx, (π i).map α ≫ β, inferInstance⟩

/-- **Algebraicity from a jointly surjective family of 1-morphisms out of categories with
formally smooth atlases.** Let `𝒴` be a category fibred in groupoids over the big fppf site of
`S` which is a stack for the fppf topology and whose diagonal is representable by algebraic
spaces. Let `q i : 𝒲 i ⟶ 𝒴` be a family of 1-morphisms, indexed by a type of cardinality below
the cofinality of the site's size cutoff, out of categories each having a formally smooth atlas,
such that every `q i` is limit preserving and formally smooth on objects and the family is
jointly surjective on objects. Then `𝒴` is an algebraic stack.

This is the closing step of the proof of **Stacks 06DC**, with `𝒲 i` the loci `𝓗_{d, lci}(𝒳/𝒴)`
and the disjoint union of the source replaced by the family: each atlas `a i` of `𝒲 i` is limit
preserving, formally smooth and surjective on objects (Stacks 06CX, by construction, Stacks
06D7), so the composites `a i ≫ q i` are scheme-valued points of `𝒴` which are limit preserving
and formally smooth on objects (Stacks 06CW and Stacks 06D2) and jointly surjective on objects
(Stacks 06D6), and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_onObjects` glues them over
the coproduct of their sources and concludes. -/
theorem isAlgebraicStack_of_jointlySurjective_formallySmoothAtlas
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (𝒲 : I → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (q : ∀ i, 𝒲 i ⟶ 𝒴) (h𝒲 : ∀ i, HasFormallySmoothAtlas B S hS (𝒲 i))
    (hlim : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS (𝒲 i) 𝒴 (q i))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS (𝒲 i) 𝒴 (q i))
    (hsurj : IsJointlySurjectiveOnObjects B S hS (fun i => (𝒲 i).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (q i))) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  choose U a ha hasurj hasmooth hafs using h𝒲
  refine isAlgebraicStack_of_jointlySurjective_forall_onObjects.{u, w} B S hS h𝒴 hdiag hI U
    (fun i => a i ≫ q i) ?_ (fun i => ?_) (fun i => ?_)
  · exact isJointlySurjectiveOnObjects_comp B S hS
      (fun i => (schemeFibredCategory B S hS (U i)).val.p) (fun i => (𝒲 i).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (a i))
      (fun i => CatFiberedInGroupoids.homFunctor (q i))
      (fun i => CatFiberedInGroupoids.homFunctor_comp_p (q i))
      (fun i => (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
        (a i) (ha i)).mpr (hasurj i)) hsurj
  · exact BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ (a i) (q i)
      (isLimitPreservingOnObjects_of_hasRelativeProperty_smooth B S hS (a i) (ha i)
        (hasmooth i)) (hlim i)
  · exact BigFppfOver.isFormallySmoothOnObjects_comp B S hS _ _ _ (a i) (q i) (hafs i) (hsm i)

end AlgebraicGeometry.Stack

end
