module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductProjectionCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative

/-!
# Stacks 06Q2 for the model of a quotient stack at a stage

Let `(X_i)` be the inverse system of the situation of Stacks 0CN4, let `G = (U, R, s, t, c)` be a
smooth groupoid in algebraic spaces over a stage `X_i` whose object and arrow spaces are of finite
presentation over `X_i`, and suppose the quotient stack `[U/R]` is algebraic. A model of `[U/R]`
is an algebraic stack `𝒳` over `S` with a 1-morphism `𝒳 ⟶ X_i` and an identification of `𝒳`
with `[U/R]` over `X_i` (`AlgebraicGeometry.Stack.StackDescentSystem.QuotientStackModel`). This
file proves that `𝒳 ⟶ X_i` is of finite presentation in the sense of Stacks 06Q2: locally of
finite presentation, quasi-compact and quasi-separated.

All three are read off the atlas `U ⟶ 𝒳`, the canonical projection of Stacks 044R followed by
the identification with the model. Algebraicity of `[U/R]` makes the projection representable by
algebraic spaces (its diagonal is), so the presentation datum of Stacks 04M9 is available, and with
it every property of the source map `s` that is stable under base change and local on the target
passes to the projection (Stacks 04X0, 06FH) and then to the atlas, by Stacks 0457.

* Local finite presentation is the smooth-diagram test of Stacks 06FM on the diagram formed by the
  atlas, the identity of `X_i` and the structure morphism `U ⟶ X_i`.
* Quasi-compactness is Stacks 050X: the atlas is surjective and its composite with `𝒳 ⟶ X_i` is
  the quasi-compact `U ⟶ X_i`.
* Quasi-separatedness is Stacks 050N part (8): `𝒳` is quasi-separated over `S` because its
  absolute diagonal is quasi-compact and quasi-separated, both properties passing from the atlas
  by the flat-cover argument of Stacks 06MB, and the relative diagonal of `X_i` over `S` is
  separated because `X_i` is an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_quasiCompact_diagonal_of_flatCover`: a
  quasi-compact surjective flat locally finitely presented 1-morphism from an absolutely
  quasi-separated algebraic space makes the absolute diagonal of its target quasi-compact.
* `AlgebraicGeometry.Stack.StackDescentSystem.modelIsFinitePresentation`: Stacks 06Q2 for the
  model of a quotient stack at a stage.

## Implementation notes

`AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_flatCover` covers properties inherited by
the first factor of a composite, which quasi-separatedness is and quasi-compactness is not; for
quasi-compactness the cancellation is made against the first projection of the self-product of the
cover, which is quasi-separated because the cover is an absolutely quasi-separated algebraic
space (Stacks 03KS).

## References

* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Quasi-compactness of the diagonal from a flat cover by a quasi-separated space -/

section QuasiCompactDiagonal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The structure 1-morphism to the final object of a category fibred in groupoids represented by
an absolutely quasi-separated algebraic space is quasi-separated in the relative sense of
Stacks 03YK: the morphism of representing presheaves leaves a quasi-separated algebraic space
(Stacks 073B). -/
theorem hasRelativeProperty_quasiSeparated_toTerminalCFG
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiSeparatedProperty B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲))
      (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒲 ⟨U, hU, ⟨eU⟩⟩) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_terminalCFG B S hS
  exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS _ _ _ U T hU hT eU eT).2
    (Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hU hUqs _)

/-- The first projection of the self-product of a category fibred in groupoids represented by an
absolutely quasi-separated algebraic space induces a quasi-separated morphism of representing
algebraic spaces: it is a base change of the structure 1-morphism to the final object. -/
theorem isQuasiSeparated_representingMap_productFstHom
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    Space.IsQuasiSeparated B S hS
      (representingMap B S hS (CatFiberedInGroupoids.product 𝒲 𝒲) 𝒲 W U eW eU
        (productFstHom B S hS 𝒲 𝒲)) := by
  have hrepT := isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒲 ⟨U, hU, ⟨eU⟩⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (productFstHom B S hS 𝒲 𝒲).hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS (terminalCFG B S hS) 𝒲 𝒲
      (toTerminalCFG B S hS 𝒲) (toTerminalCFG B S hS 𝒲) hrepT
  exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.quasiSeparatedProperty B S hS) (productFstHom B S hS 𝒲 𝒲) hrep W U hW hU eW eU).1
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.quasiSeparatedProperty B S hS)
      𝒲 (terminalCFG B S hS) 𝒲
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲))
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲))
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲)))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲))
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒲)))
      (hasRelativeProperty_quasiSeparated_toTerminalCFG B S hS hZ 𝒲 U hU hUqs eU))

/-- **Cancelling the product projection at quasi-compactness.** Let `f : 𝒲 ⟶ 𝒳` be representable
by algebraic spaces with `𝒲` represented by an absolutely quasi-separated algebraic space `U`, and
let `V` and `W` represent `𝒲 ×_𝒳 𝒲` and `𝒲 × 𝒲`. If the first projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲` is
quasi-compact relatively, then so is the morphism `V ⟶ W` induced by the projection to the
product: its composite with the quasi-separated first projection `W ⟶ U` is (Stacks 03KS). -/
theorem isQuasiCompact_representingMap_relativeDiagonalSquare_fst
    (𝒲 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒲 ⟶ 𝒳)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS)
      (Bicategory.InducedBicategory.mkHom (twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom))
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf)) :
    Space.quasiCompactProperty B S hS (ObjectProperty.homMk
        (representingMap B S hS (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt
          (CatFiberedInGroupoids.product 𝒲 𝒲) V W eV eW
          (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst) :
      (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      ((relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst ≫
        productFstHom B S hS 𝒲 𝒲).hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf
  have hcomposite := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.quasiCompactProperty B S hS)
    ((relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst ≫ productFstHom B S hS 𝒲 𝒲)
    hrep V U hV hU eV eU).1 hP
  rw [representingMap_comp B S hS V W U eV eW eU] at hcomposite
  exact Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ hV hU hcomposite
    (isQuasiSeparated_representingMap_productFstHom B S hS hZ 𝒲 U hU hUqs eU W hW eW)

/-- **A quasi-compact flat cover by an absolutely quasi-separated algebraic space makes the
absolute diagonal quasi-compact.** Let `f : 𝒲 ⟶ 𝒳` be a surjective, flat, locally finitely
presented 1-morphism of algebraic stacks over `S`, with `𝒲` represented by an absolutely
quasi-separated algebraic space. If `f` is quasi-compact in the relative sense of Stacks 03YK,
then so is the absolute diagonal of `𝒳`.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_flatCover` at
quasi-compactness, which is not inherited by first factors in general: the cancellation is
performed against the first projection of `𝒲 × 𝒲`, which is quasi-separated because `𝒲` is. -/
theorem hasRelativeProperty_quasiCompact_diagonal_of_flatCover
    {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ U)
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (hSurj : IsSurjective B S hS f)
    (hFlat : AlgebraicStacks.IsFlat B S hS f)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS) f.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
        ⟨U, hU, ⟨eU⟩⟩ f.hom)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS)
      (diagonal.{u, u, u + 1} B S hS 𝒳.val)
      (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳) := by
  have h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val := ⟨U, hU, ⟨eU⟩⟩
  have hfr : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒲 f.hom
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_product B S hS 𝒲.val 𝒲.val h𝒲 h𝒲
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    𝒳.val 𝒲.val 𝒲.val f.hom.hom f.hom.hom hfr h𝒲
  exact hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS
    (Space.quasiCompactProperty B S hS) 𝒳.val
    (CatFiberedInGroupoids.product 𝒳.val 𝒳.val) (CatFiberedInGroupoids.product 𝒲.val 𝒲.val)
    (diagonal.{u, u, u + 1} B S hS 𝒳.val) (CatFiberedInGroupoids.productMap f.hom f.hom)
    (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳)
    (localEssSurj_productMap_of_flatCover B S hS f h𝒲 hSurj hFlat hLfp)
    (relativeDiagonalSquare.{u, u, u} B S hS 𝒲.val 𝒲.val 𝒳.val f.hom f.hom)
    (isTwoFibreProduct_relativeDiagonalSquare.{u, u, u} B S hS 𝒲.val 𝒲.val 𝒳.val f.hom f.hom)
    V W hV hW eV eW
    (isQuasiCompact_representingMap_relativeDiagonalSquare_fst B S hS hZ 𝒲.val 𝒳.val f.hom hfr
      U hU hUqs eU V W hV hW eV eW
      (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.quasiCompactProperty B S hS)
        𝒲.val 𝒳.val 𝒲.val f.hom f.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom f.hom) hP))

end QuasiCompactDiagonal

namespace QuotientStackModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {Y : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS Y} (M : QuotientStackModel.{u, w} Y G)

/-- The atlas `U ⟶ [U/R]` of Stacks 044R read on the model: the canonical projection of the
object space followed by the equivalence onto the model. -/
noncomputable def projection :
    algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property ⟶ M.stack :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (quotientStackProjection G) M.equivOver.equiv.functor))

/-- The square comparing the model atlas with the canonical projection of Stacks 044R, whose two
horizontal 1-morphisms are the universe lift of the object space and the inverse of the
equivalence onto the model. -/
noncomputable def projectionSquareIso :
    BasedFunctor.comp (liftedFibredCategoryUp G.objects) (quotientStackProjectionHom G).hom ≅
      BasedFunctor.comp M.projection.hom.hom M.equivOver.equiv.inverse :=
  (BasedCategory.isoWhiskerLeft (quotientStackProjection G) M.equivOver.equiv.unitIso).symm

variable {M} in
/-- The canonical projection of an algebraic quotient stack is representable by algebraic spaces:
its target has representable diagonal. -/
theorem representable_quotientStackProjectionHom_of_isAlgebraicStack
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G)) :
    IsRepresentableByAlgebraicSpaces B S hS (quotientStackProjectionHom G).hom := by
  obtain ⟨_, _, hdiag, _⟩ := halg
  exact isRepresentableByAlgebraicSpaces_quotientStackProjectionHom_of_hasRepresentableDiagonal
    B S hS G hdiag

/-- The two comparison 1-morphisms between the model atlas and the canonical projection are
equivalences. -/
private theorem isEquivalence_inverse_and_liftedFibredCategoryUp :
    Functor.IsEquivalence (show M.stack.val.val ⥤ᵇ
      (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G)).val
      from M.equivOver.equiv.inverse).toFunctor ∧
    Functor.IsEquivalence (show (fibredCategory B S hS G.objects.obj).val ⥤ᵇ
      (liftedObjectSpace G).val from liftedFibredCategoryUp G.objects).toFunctor :=
  ⟨M.equivOver.equiv.equiv.isEquivalence_inverse, isEquivalence_liftedFibredCategoryUp G.objects⟩

/-- The model atlas is representable by algebraic spaces. -/
theorem representable_projection (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G)) :
    IsRepresentableByAlgebraicSpaces B S hS M.projection.hom.hom := by
  obtain ⟨_, _⟩ := M.isEquivalence_inverse_and_liftedFibredCategoryUp
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS M.projection.hom.hom
    (quotientStackProjectionHom G).hom (liftedFibredCategoryUp G.objects)
    M.equivOver.equiv.inverse M.projectionSquareIso).1
    (representable_quotientStackProjectionHom_of_isAlgebraicStack halg)

/-- **Stacks 04X0 and 06FH read on the model.** Every property of morphisms of algebraic spaces
stable under base change and local on the target that the source map of the groupoid has, the
model atlas has relatively. -/
theorem hasRelativeProperty_projection
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)] (hP : P G.source) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P M.projection.hom
      (M.representable_projection halg) := by
  obtain ⟨_, _⟩ := M.isEquivalence_inverse_and_liftedFibredCategoryUp
  exact hasRelativeProperty_of_equivalences B S hS P M.projection.hom
    (quotientStackProjectionHom G) (liftedFibredCategoryUp G.objects)
    M.equivOver.equiv.inverse M.projectionSquareIso
    (representable_quotientStackProjectionHom_of_isAlgebraicStack halg)
    (M.representable_projection halg)
    (QuotientAtlas.hasRelativeProperty_of_representable.{u, u}
      (representable_quotientStackProjectionHom_of_isAlgebraicStack halg) P hP)

/-- **Stacks 044R through the model.** The model atlas followed by the structure morphism of the
model is 2-isomorphic to the 1-morphism of Stacks 0458 attached to the structure morphism of the
object space. -/
noncomputable def projectionCompIso :
    BasedFunctor.comp M.projection.hom.hom M.structureMorphism.hom.hom ≅
      (associatedMap B S hS G.objectsToBase.hom).1.hom :=
  BasedCategory.isoWhiskerLeft (quotientStackProjection G) M.equivOver.compIso ≪≫
    eqToIso (quotientStackProjection_comp_toBase G)

/-- The model atlas is smooth in the relative sense of Stacks 04XB. -/
theorem isRelativelySmooth_projection
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    IsRelativelySmooth B S hS M.projection.hom :=
  ⟨M.representable_projection halg,
    M.hasRelativeProperty_projection halg (Space.smoothMorphismProperty B S hS) hsm.source⟩

/-- The model atlas is surjective on objects (Stacks 06D4). -/
theorem isSurjectiveOnObjects_projection
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G)) :
    IsSurjectiveOnObjects B S hS
      (algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property).val.val.p
      M.stack.val.val.p (CatFiberedInGroupoids.homFunctor M.projection.hom) :=
  (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS M.projection.hom
    (M.representable_projection halg)).2
    (M.hasRelativeProperty_projection halg (Space.surjectiveMorphismProperty B S hS)
      (QuotientAtlas.isSurjective_source G))

/-- **Stacks 06Q2, part (1), for the model.** The structure morphism of the model of the
quotient stack of a smooth groupoid whose object space is locally of finite presentation over the
stage is locally of finite presentation: the model atlas, the identity of the stage and the
structure morphism of the object space form a diagram of Stacks 06FM over it. -/
theorem isLocallyOfFinitePresentation_structureMorphism
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (hU : Space.IsLocallyOfFinitePresentation B S hS G.objectsToBase.hom) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS M.structureMorphism :=
  hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) _
    ⟨G.objects.obj, Y.obj, G.objects.property, Y.property,
      M.projection.hom, 𝟙 _, G.objectsToBase.hom,
      ⟨Bicategory.rightUnitor _ ≪≫
        Bicategory.InducedBicategory.isoMk M.projectionCompIso.symm⟩,
      M.isRelativelySmooth_projection halg hsm, M.isSurjectiveOnObjects_projection halg,
      isRelativelySmooth_id B S hS
        (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ Y.property),
      hU⟩

variable {M} in
/-- The structure morphism of the object space to the stage, as a 1-morphism of algebraic stacks
over `S`: the 1-morphism of Stacks 0458 attached to it. -/
noncomputable abbrev objectsToStage :
    algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property ⟶
      algebraicSpaceStack.{u, w} B S hS Y.obj Y.property :=
  Bicategory.InducedBicategory.mkHom (associatedMap B S hS G.objectsToBase.hom).1

/-- The model atlas is surjective (Stacks 04ZS). -/
theorem isSurjective_projection (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G)) :
    IsSurjective B S hS M.projection :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS M.projection
    (M.representable_projection halg)).2
    (M.hasRelativeProperty_projection halg (Space.surjectiveMorphismProperty B S hS)
      (QuotientAtlas.isSurjective_source G))

variable {M} in
/-- The 1-morphism of Stacks 0458 attached to a quasi-compact structure morphism of the object
space is quasi-compact in the sense of Stacks 050U. -/
theorem isQuasiCompactMorphism_objectsToStage
    (hUqc : Space.IsQuasiCompact B S hS G.objectsToBase.hom) :
    IsQuasiCompactMorphism.{u, w} B S hS (objectsToStage (Y := Y) (G := G)) :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS _
    (isRepresentableByAlgebraicSpaces_associatedMap (X := G.objects) (Y := Y)
      G.objectsToBase.hom)).1
    ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS (Space.quasiCompactProperty B S hS)
      (associatedMap B S hS G.objectsToBase.hom).1
      (isRepresentableByAlgebraicSpaces_associatedMap (X := G.objects) (Y := Y)
        G.objectsToBase.hom)
      G.objects.obj Y.obj G.objects.property Y.property
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).2
      (by
        change Space.IsQuasiCompact B S hS (representingMap B S hS _ _ _ _ _ _ _)
        rw [representingMap_associatedMap]
        exact hUqc))

/-- **Stacks 06Q2, quasi-compactness, for the model.** The structure morphism of the model is
quasi-compact: the model atlas is surjective and its composite with the structure morphism is the
quasi-compact structure morphism of the object space (Stacks 050X). -/
theorem isQuasiCompactMorphism_structureMorphism
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hUqc : Space.IsQuasiCompact B S hS G.objectsToBase.hom) :
    IsQuasiCompactMorphism.{u, w} B S hS M.structureMorphism :=
  isQuasiCompactMorphism_of_comp_of_isSurjective B S hS M.projection objectsToStage
    M.structureMorphism (isoMkAlgebraicStacks B S hS M.projectionCompIso)
    (M.isSurjective_projection halg) (isQuasiCompactMorphism_objectsToStage hUqc)

/-- The model atlas is flat (Stacks 06PW): the source map of a smooth groupoid is flat. -/
theorem isFlat_projection (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    AlgebraicStacks.IsFlat B S hS M.projection := by
  have hBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS _ M.stack.property
    M.projection.hom (M.representable_projection halg)
    (M.hasRelativeProperty_projection halg _
      (Space.isFlat_of_isSmooth B S hS _ hsm.source))

/-- The model atlas is locally of finite presentation (Stacks 06Q2, part (1)): the source map of a
smooth groupoid is. -/
theorem isLocallyOfFinitePresentation_projection
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS M.projection := by
  have hBC : (spaceProperty B S hS (fun _ _ h =>
      Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hLT : (spaceProperty B S hS (fun _ _ h =>
      Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property).property
    M.stack.property M.projection.hom (M.representable_projection halg)
    (M.hasRelativeProperty_projection halg _
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm.source))

variable {M} in
/-- The source map of a groupoid whose object and arrow spaces are of finite presentation over
the stage is quasi-compact (Stacks 03KS against the quasi-separated object space). -/
theorem isQuasiCompact_source
    (hU : Space.IsFinitePresentation B S hS G.objectsToBase.hom)
    (hR : Space.IsFinitePresentation B S hS G.arrowsToBase.hom) :
    Space.IsQuasiCompact B S hS G.source.hom := by
  have h : G.source.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
    congrArg (fun k => k.hom) G.source_over
  exact Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ G.arrows.property
    Y.property (h ▸ hR.2.1) hU.2.2

variable {M} in
/-- The source map of a groupoid whose arrow space is quasi-separated over the stage is
quasi-separated (Stacks 03KR). -/
theorem isQuasiSeparated_source
    (hR : Space.IsFinitePresentation B S hS G.arrowsToBase.hom) :
    Space.IsQuasiSeparated B S hS G.source.hom := by
  have h : G.source.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
    congrArg (fun k => k.hom) G.source_over
  exact Space.isQuasiSeparated_of_comp B S hS _ _ (h ▸ hR.2.2)

/-- **The model is quasi-separated over `S`.** Its absolute diagonal is quasi-compact and
quasi-separated: both properties pass from the model atlas, which has them because the source map
does, by the flat-cover argument of Stacks 06MB; the object space is absolutely quasi-separated,
being of finite presentation over the quasi-separated stage. -/
theorem isQuasiSeparatedOver_stack (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ Y.obj)
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (hU : Space.IsFinitePresentation B S hS G.objectsToBase.hom)
    (hR : Space.IsFinitePresentation B S hS G.arrowsToBase.hom) :
    IsQuasiSeparatedOver B S hS M.stack := by
  have hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ G.objects.obj :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ G.objects.property
      hYqs hU.2.2
  have hqc := hasRelativeProperty_quasiCompact_diagonal_of_flatCover B S hS hZ M.projection
    G.objects.obj G.objects.property hUqs (StacksRepresentableCFG.EquivalenceOver.refl _)
    (M.isSurjective_projection halg) (M.isFlat_projection halg hsm)
    (M.isLocallyOfFinitePresentation_projection halg hsm)
    (M.hasRelativeProperty_projection halg (Space.quasiCompactProperty B S hS)
      (isQuasiCompact_source hU hR))
  have hqs := hasRelativeProperty_diagonal_of_flatCover B S hS
    (Space.quasiSeparatedProperty B S hS) M.projection
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ G.objects.property)
    (M.isSurjective_projection halg) (M.isFlat_projection halg hsm)
    (M.isLocallyOfFinitePresentation_projection halg hsm)
    (fun {_ _ _} a b h => Space.isQuasiSeparated_of_comp B S hS a.hom b.hom h)
    (M.hasRelativeProperty_projection halg (Space.quasiSeparatedProperty B S hS)
      (isQuasiSeparated_source hR))
  exact ⟨(relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS M.stack
      (Space.quasiCompactProperty B S hS)).mp hqc,
    (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS M.stack
      (Space.quasiSeparatedProperty B S hS)).mp hqs⟩

variable {M} in
/-- The relative diagonal of the structure morphism of the stage is quasi-separated: the
structure morphism of an algebraic space is representable by algebraic spaces, so its relative
diagonal is a monomorphism and hence separated (Stacks 04YQ). -/
theorem isQuasiSeparated_relativeDiagonal_structureMorphism_stage :
    Stack.IsQuasiSeparated B S hS
      (relativeDiagonalAlgebraicStacks B S hS
        (Stack.structureMorphism.{u, w} B S hS
          (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property))).hom := by
  obtain ⟨-, hsep⟩ := isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
    (Stack.structureMorphism.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property))
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ Y.property)
      (Stack.structureMorphism.{u, w} B S hS
        (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)).hom)
  intro U y hy F hF hE
  exact Space.isQuasiSeparated_of_isSeparated B S hS (hsep U y hy F hF hE)

/-- **Stacks 06Q2, quasi-separatedness, for the model.** The structure morphism of the model is
quasi-separated: the model is quasi-separated over `S` and the stage has quasi-separated relative
diagonal over `S`, so Stacks 050N part (8) applies. -/
theorem isQuasiSeparated_structureMorphism
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ Y.obj)
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (hU : Space.IsFinitePresentation B S hS G.objectsToBase.hom)
    (hR : Space.IsFinitePresentation B S hS G.arrowsToBase.hom) :
    AlgebraicStacks.IsQuasiSeparated B S hS M.structureMorphism :=
  AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS M.structureMorphism
    (M.isQuasiSeparatedOver_stack hYqs halg hsm hU hR)
    isQuasiSeparated_relativeDiagonal_structureMorphism_stage

end QuotientStackModel

namespace StackDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I]

variable (C : StackDescentSystem B S hS hZ I) in
/-- **Stacks 06Q2 for the model of a quotient stack at a stage.** The model of the quotient stack
of a smooth groupoid in algebraic spaces over a stage `X_i`, whose object and arrow spaces are of
finite presentation over `X_i`, is of finite presentation over `X_i`. -/
theorem modelIsFinitePresentation : C.ModelIsFinitePresentation.{u, w} := by
  intro i G M hsm hU hR
  have halg := isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hsm
  exact ⟨M.toModel.isLocallyOfFinitePresentation_structureMorphism halg hsm hU.1,
    M.toModel.isQuasiCompactMorphism_structureMorphism halg hU.2.1,
    M.toModel.isQuasiSeparated_structureMorphism (C.stage_quasiSeparated i) halg hsm hU hR⟩

end StackDescentSystem

end AlgebraicGeometry.Stack

end
