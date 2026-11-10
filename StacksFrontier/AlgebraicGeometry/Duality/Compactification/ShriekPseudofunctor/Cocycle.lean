module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekPseudofunctor.TripleCompactification

/-!
# Exceptional inverse image is a pseudofunctor (Tag 0ATY): the cocycle condition

The comparison of the rectangle `A + B` with the choice for `f` and `h ∘ g`
(`Stacks.Duality.CompositionData.tripleComparison`, through
`Stacks.Duality.CompositionData.triplePsi`), the cocycle identity for the triple of
compactifications, and **the cocycle condition** `Stacks.Duality.upperShriekCompIsoAtModel_cocycle`:
for composable `f`, `g`, `h` and any compactifications of `h ∘ g ∘ f`, `f`, `h ∘ g`, `g`, `h`,
`g ∘ f`, the two ways of identifying `(h ∘ g ∘ f)^!` with `f^! ∘ g^! ∘ h^!` through
`Stacks.Duality.upperShriekCompIsoAtModel` agree.

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S]

section Triple

variable {X Y Z T : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (E : CompositionData g h) (t : CompactificationOf (Over.mk (f.left ≫ E.top.immersion)))

namespace CompositionData

/-! ### Comparing the rectangle `A + B` with the choice for `f` and `h ∘ g` -/

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The square `E` for the identity of the compactification `X ⟶ X̄ ⟶ T`. -/
theorem tripleSqE : IsPullback (tripleLeft E t).topImm (𝟙 X.left)
    (𝟙 t.space)
    (tripleLeft E t).topImm :=
  (CompactificationOf.isPullback_of_preservesInterior _
    (CompactificationOf.preservesInterior_id _)).flip

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The square `D` for the identity of the compactification `Y ⟶ Ȳ ⟶ T`. -/
theorem tripleSqD : IsPullback E.topImm (𝟙 Y.left)
    (𝟙 E.top.space) E.topImm :=
  (CompactificationOf.isPullback_of_preservesInterior _
    (CompactificationOf.preservesInterior_id _)).flip

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The square `A` for the comparison `U' ⟶ U`. -/
theorem tripleSqA : IsPullback (tripleInner E t).innerImmersion (𝟙 X.left)
    (tripleComparison E t) (tripleLeft E t).innerImmersion :=
  (CompactificationOf.isPullback_of_preservesInterior _
    (preservesInterior_tripleComparisonHom E t)).flip

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The square `F` for the comparison `U' ⟶ U`, over the identity of `X̄`. -/
theorem tripleSqF :
    IsPullback ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space)
    (tripleComparison E t)
    (𝟙 t.space)
    (tripleLeft E t).innerFst :=
  @IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ (isIso_tripleComparison E t)
    (inferInstanceAs (IsIso (𝟙 t.space)))
    ⟨((Category.comp_id _).trans (tripleComparison_fst E t).symm)⟩

/-- The base change map of the square `E`. -/
abbrev tripleBcE :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionTopImm (tripleLeft E t))
    (instIsOpenImmersionTopImm (tripleLeft E t)) (tripleSqE E t)

/-- The base change map of the square `D`. -/
abbrev tripleBcD :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionTopImm E) (instIsOpenImmersionTopImm E)
    (tripleSqD E)

/-- The base change map of the square `A`. -/
abbrev tripleBcA :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionInnerImmersion (tripleInner E t))
    (instIsOpenImmersionInnerImmersion (tripleLeft E t)) (tripleSqA E t)

/-- `α_E` for the identity of the compactification `X ⟶ X̄ ⟶ T`. -/
abbrev tripleAlphaE :=
  alphaNat (congrN (Category.id_comp (tripleLeft E t).outer.toBase).symm ≪≫
      compN (𝟙 t.space) (tripleLeft E t).outer.toBase)
    (tripleBcE E t) (idN X.left)

/-- `α_D` for the identity of the compactification `Y ⟶ Ȳ ⟶ T`. -/
abbrev tripleAlphaD :=
  alphaNat (congrN (Category.id_comp E.outer.toBase).symm ≪≫ compN (𝟙 E.top.space) E.outer.toBase)
    (tripleBcD E) (idN Y.left)

/-- `α_A` for the comparison `U' ⟶ U`. -/
abbrev tripleAlphaA :=
  alphaNat (congrN (tripleComparison_snd E t).symm ≪≫
      compN (tripleComparison E t) (tripleLeft E t).innerSnd)
    (tripleBcA E t) (idN X.left)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `X̄ ⟶ Ȳ` followed by the identity of `Ȳ` is the identity of `X̄` followed by `X̄ ⟶ Ȳ`. -/
theorem tripleHp' : t.toBase ≫
      (𝟙 E.top.space) =
    (𝟙 t.space) ≫ t.toBase :=
  (Category.comp_id _).trans (Category.id_comp _).symm

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The projection `U' ⟶ Y` followed by the identity of `Y` is `U' ⟶ U ⟶ Y`. -/
theorem tripleHq' : (tripleInner E t).innerSnd ≫ 𝟙 Y.left =
    tripleComparison E t ≫ (tripleLeft E t).innerSnd :=
  (Category.comp_id _).trans (tripleComparison_snd E t).symm

/-- The base change map of the square `F`. -/
abbrev tripleBcF :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionInnerFst (tripleLeft E t)) (tripleSqF E t)

/-- The base change map of the row of `A` and `F`. -/
abbrev tripleBcAF :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _
    (@IsOpenImmersion.comp _ _ _ _ _ (instIsOpenImmersionInnerImmersion (tripleInner E t))
      (isOpenImmersion_tripleRow E t))
    (@IsOpenImmersion.comp _ _ _ _ _ (instIsOpenImmersionInnerImmersion (tripleLeft E t))
      (instIsOpenImmersionInnerFst (tripleLeft E t)))
    ((tripleSqA E t).paste_horiz (tripleSqF E t))

/-- The base change map of the stack of `F` over the square of the choice for `f` and `h ∘ g`. -/
abbrev tripleBcFB :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionBaseImm (tripleLeft E t))
    ((tripleSqF E t).paste_vert (tripleLeft E t).isPullback_innerFst)

/-- The base change map of the stack of the rectangle `A + B` over `D`. -/
abbrev tripleBcCD :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t) (instIsOpenImmersionTopImm E)
    ((isPullback_tripleRow E t).paste_vert (tripleSqD E))

/-- The base change map of the square `E` is that of the row of `A` and `F`, up to the transports
along `X ⟶ X̄ = X ⟶ U' ⟶ X̄` and `X ⟶ X̄ = X ⟶ U ⟶ X̄`. -/
theorem tripleE_congr :
    tripleBcE E t =
      whiskerLeft (tw (𝟙 t.space))
          (pbCongrN (tripleRow_immersion E t).symm).hom ≫
        tripleBcAF E t ≫
          whiskerRight (pbCongrN (tripleLeft E t).innerImmersion_fst.symm).inv (tw (𝟙 X.left)) :=
  @bcN_congr_horiz _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (@IsOpenImmersion.comp _ _ _ _ _ (instIsOpenImmersionInnerImmersion (tripleInner E t))
      (isOpenImmersion_tripleRow E t))
    (instIsOpenImmersionTopImm (tripleLeft E t))
    (@IsOpenImmersion.comp _ _ _ _ _ (instIsOpenImmersionInnerImmersion (tripleLeft E t))
      (instIsOpenImmersionInnerFst (tripleLeft E t)))
    (instIsOpenImmersionTopImm (tripleLeft E t))
    (tripleRow_immersion E t).symm (tripleLeft E t).innerImmersion_fst.symm
    ((tripleSqA E t).paste_horiz (tripleSqF E t)) (tripleSqE E t)

open scoped CategoryTheory.TwoSquare in
/-- The base change map of the row of `A` and `F` is the horizontal composite of those of `A`
and `F`. -/
theorem tripleAF_hcomp :
    tripleBcAF E t =
      (((TwoSquare.mk _ _ _ _ (tripleBcF E t) ≫ᵥ TwoSquare.mk _ _ _ _ (tripleBcA E t)).whiskerLeft
        (pbCompN (tripleLeft E t).innerImmersion (tripleLeft E t).innerFst).hom).whiskerRight
          (pbCompN (tripleInner E t).innerImmersion
            ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst :
              _ ⟶ t.space)).inv) :=
  @bcN_hcomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (instIsOpenImmersionInnerImmersion (tripleInner E t)) (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionInnerImmersion (tripleLeft E t))
    (instIsOpenImmersionInnerFst (tripleLeft E t))
    (tripleSqA E t) (tripleSqF E t)

open scoped CategoryTheory.TwoSquare in
/-- The base change map of the stack of `F` over the square of the choice for `f` and `h ∘ g` is
the vertical composite of their base change maps. -/
theorem tripleFB_vcomp :
    tripleBcFB E t =
      ((TwoSquare.mk _ _ _ _ (tripleLeft E t).baseChange ≫ₕ
        TwoSquare.mk _ _ _ _ (tripleBcF E t)).whiskerTop
        (compN (𝟙 t.space) t.toBase).hom).whiskerBottom
        (compN (tripleComparison E t) (tripleLeft E t).innerSnd).inv :=
  @bcN_vcomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionInnerFst (tripleLeft E t)) (instIsOpenImmersionBaseImm (tripleLeft E t))
    (tripleSqF E t) (tripleLeft E t).isPullback_innerFst

open scoped CategoryTheory.TwoSquare in
/-- The base change map of the stack of the rectangle `A + B` over `D` is the vertical composite
of their base change maps. -/
theorem tripleCD_vcomp :
    tripleBcCD E t =
      ((TwoSquare.mk _ _ _ _ (tripleBcD E) ≫ₕ
        TwoSquare.mk _ _ _ _ (tripleRowBaseChange E t)).whiskerTop
        (compN t.toBase (𝟙 E.top.space)).hom).whiskerBottom
        (compN (tripleInner E t).innerSnd (𝟙 Y.left)).inv :=
  @bcN_vcomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionTopImm E) (instIsOpenImmersionTopImm E)
    (isPullback_tripleRow E t) (tripleSqD E)

/-- The base change map of the stack of `A + B` over `D` is that of the stack of `F` over the
square of the choice for `f` and `h ∘ g`, up to the transports along `tripleHp'` and
`tripleHq'`. -/
theorem tripleCD_congr :
    tripleBcCD E t =
      whiskerRight (congrN (tripleHp' E t)).hom
          (pb ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space)) ≫
        tripleBcFB E t ≫ whiskerLeft (pb E.topImm) (congrN (tripleHq' E t)).inv :=
  @bcN_congr_vert _ _ _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
    (instIsOpenImmersionTopImm E)
    (tripleHq' E t) (tripleHp' E t)
    ((isPullback_tripleRow E t).paste_vert (tripleSqD E))
    ((tripleSqF E t).paste_vert (tripleLeft E t).isPullback_innerFst)

/-- The instance of `compN_square_nat` for the identities of `X̄` and `Ȳ` over `X̄ ⟶ Ȳ`. -/
theorem tripleH5 :
    (congrN (Category.id_comp (tripleLeft E t).outer.toBase).symm ≪≫
        compN (𝟙 t.space) (tripleLeft E t).outer.toBase).hom ≫
        whiskerRight (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase).hom
          (tw (𝟙 t.space)) =
      (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase).hom ≫
        whiskerRight (congrN (Category.id_comp E.outer.toBase).symm ≪≫
          compN (𝟙 E.top.space) E.outer.toBase).hom (tw t.toBase) ≫
        whiskerLeft (tw E.outer.toBase) ((compN t.toBase (𝟙 E.top.space)).inv ≫
          (congrN (tripleHp' E t)).hom ≫ (compN (𝟙 t.space) t.toBase).hom) :=
  compN_square_nat t.toBase t.toBase (𝟙 t.space) (𝟙 E.top.space) E.outer.toBase E.outer.toBase
    (Category.id_comp _) (tripleHp' E t) (Category.id_comp (tripleLeft E t).outer.toBase).symm

/-- The instance of `compN_unit_nat` for the comparison `U' ⟶ U` over `Y`. -/
theorem tripleH6 :
    (congrN (tripleComparison_snd E t).symm ≪≫
        compN (tripleComparison E t) (tripleLeft E t).innerSnd).hom =
      whiskerRight (idN Y.left).inv (tw (tripleInner E t).innerSnd) ≫
        (compN (tripleInner E t).innerSnd (𝟙 Y.left)).inv ≫ (congrN (tripleHq' E t)).hom ≫
          (compN (tripleComparison E t) (tripleLeft E t).innerSnd).hom :=
  compN_unit_nat (tripleInner E t).innerSnd (tripleLeft E t).innerSnd (tripleComparison E t)
    (tripleComparison_snd E t) (tripleHq' E t)

/-- **The comparison of [Stacks, Tag 0ATX] for `f` and `h ∘ g`, read on the rectangle `A + B`, is
the one of the choice for `f` and `h ∘ g` read through the comparison `α_A` of [Stacks, Tag 0AA0]
for `U' ⟶ U`**, as an identity of transformations, up to the comparisons `α_E` and `α_D` of the
identities: an instance of the chase of the proof of [Stacks, Tag 0ATX]. -/
theorem triplePsi :
    tripleAlphaE E t ≫ (tripleLeft E t).compMap =
      tripleRowMap E t ≫
        whiskerLeft (tw (tripleLeft E t).base.toBase ⋙ pb (tripleLeft E t).baseImm)
          (tripleAlphaA E t) ≫
        whiskerRight (tripleAlphaD E)
          (tw (tripleLeft E t).innerSnd ⋙ pb (tripleLeft E t).innerImmersion) :=
  compositionChaseNat
    (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase)
    (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase)
    (pbCongrN (tripleRow_immersion E t).symm) (pbCongrN (tripleLeft E t).innerImmersion_fst.symm)
    (pbCompN (tripleInner E t).innerImmersion
      ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space))
    (pbCompN (tripleLeft E t).innerImmersion (tripleLeft E t).innerFst)
    (tripleRowRestrict E t) (tripleLeft E t).restrictCompIso rfl rfl
    (tripleRowBaseChange E t) (tripleLeft E t).baseChange
    (congrN (Category.id_comp (tripleLeft E t).outer.toBase).symm ≪≫
      compN (𝟙 t.space) (tripleLeft E t).outer.toBase)
    (tripleBcE E t) (idN X.left)
    (congrN (Category.id_comp E.outer.toBase).symm ≪≫ compN (𝟙 E.top.space) E.outer.toBase)
    (tripleBcD E) (idN Y.left)
    (congrN (tripleComparison_snd E t).symm ≪≫
      compN (tripleComparison E t) (tripleLeft E t).innerSnd)
    (tripleBcA E t) (tripleBcF E t) (tripleBcAF E t)
    (compN (𝟙 t.space) t.toBase)
    (compN (tripleComparison E t) (tripleLeft E t).innerSnd)
    (compN t.toBase (𝟙 E.top.space))
    (compN (tripleInner E t).innerSnd (𝟙 Y.left))
    (congrN (tripleHp' E t)) (congrN (tripleHq' E t))
    (tripleBcFB E t) (tripleBcCD E t)
    (tripleE_congr E t) (tripleAF_hcomp E t) (tripleFB_vcomp E t) (tripleCD_vcomp E t)
    (tripleCD_congr E t) (tripleH5 E t) (tripleH6 E t)

/-! ### Reading the comparisons on the bounded-below part -/

/-- `α_E` is the comparison of [Stacks, Tag 0AA0] for the identity of `X ⟶ X̄ ⟶ T`. -/
theorem tripleAlphaE_hom :
    (refinementIso (f ≫ g ≫ h) (𝟙 (tripleLeft E t).outer)
      (CompactificationOf.preservesInterior_id _)).hom =
      whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel T.left))
        (tripleAlphaE E t) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

/-- The comparison of [Stacks, Tag 0AA0] for the identity of a compactification is the identity. -/
private theorem refinementIso_id_hom {A B : FTS S} {a : A ⟶ B}
    (k : CompactificationOf (Over.mk a.left)) :
    (refinementIso a (𝟙 k) (CompactificationOf.preservesInterior_id _)).hom = 𝟙 _ := by
  rw [← compactificationUpperShriekIso_eq_iso, compactificationUpperShriekIso_refl]
  rfl

/-- `α_E` is the identity on the bounded-below part. -/
theorem tripleAlphaE_one :
    whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel T.left))
      (tripleAlphaE E t) = 𝟙 _ := by
  rw [← tripleAlphaE_hom]
  exact refinementIso_id_hom _

/-- `α_D` is the comparison of [Stacks, Tag 0AA0] for the identity of `Y ⟶ Ȳ ⟶ T`. -/
theorem tripleAlphaD_hom :
    (refinementIso (g ≫ h) (𝟙 E.outer) (CompactificationOf.preservesInterior_id _)).hom =
      whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel T.left))
        (tripleAlphaD E) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

/-- `α_D` is the identity on the bounded-below part. -/
theorem tripleAlphaD_one :
    whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel T.left))
      (tripleAlphaD E) = 𝟙 _ := by
  rw [← tripleAlphaD_hom]
  exact refinementIso_id_hom _

/-- `α_A` is the comparison of [Stacks, Tag 0AA0] for `U' ⟶ U`. -/
theorem tripleAlphaA_hom :
    (refinementIso f (tripleComparisonHom E t) (preservesInterior_tripleComparisonHom E t)).hom =
      whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
        (tripleAlphaA E t) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The compactification `X ⟶ V ⟶ Z` of `g ∘ f` of the choice for `g ∘ f` and `h` is the
compactification `X ⟶ V ⟶ W ⟶ Z` of the choice for `f` and `g`. -/
theorem tripleRight_inner_eq : (tripleRight E t).inner = (tripleInner E t).outer :=
  @CompactificationOf.ofFactorization_congr _ _ _ (tripleRight E t).innerSpace
    (tripleRight E t).innerImmersion (tripleRight E t).innerSnd (tripleMap E t ≫ E.innerSnd)
    inferInstance inferInstance
    (by have := isProper_tripleMap E t; infer_instance)
    (tripleRight E t).innerImmersion_snd
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ E.innerSnd)
      (tripleRight_innerImmersion_tripleMap E t)).trans
      ((Category.assoc _ _ _).trans (congrArg (f.left ≫ ·) E.innerImmersion_snd))))
    (tripleMap_snd E t).symm

/-- The comparison of [Stacks, Tag 0AA0] between the two equal compactifications of `g ∘ f` is the
transport along `V ⟶ Z = V ⟶ W ⟶ Z`. -/
theorem tripleTransport :
    (compactificationUpperShriekIso (f ≫ g) (tripleRight E t).inner (tripleInner E t).outer).hom =
      whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
        (whiskerRight (congrN (tripleMap_snd E t).symm).hom
          (pb (tripleRight E t).innerImmersion)) :=
  compactificationUpperShriekIso_ofFactorization (f ≫ g) (tripleRight E t).innerSpace
    (tripleRight E t).innerImmersion _ _ (tripleMap_snd E t).symm

/-- The comparison of [Stacks, Tag 0AA0] between the compactifications `U'` and `U` of `f` is
`α_A`. -/
theorem tripleAlphaA_hom' :
    (compactificationUpperShriekIso f (tripleInner E t).inner (tripleLeft E t).inner).hom =
      whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
        (tripleAlphaA E t) := by
  rw [compactificationUpperShriekIso_eq_iso f (tripleComparisonHom E t)
    (preservesInterior_tripleComparisonHom E t)]
  exact tripleAlphaA_hom E t

/-- **The cocycle identity of [Stacks, Tag 0ATY] for the triple of compactifications**, as an
identity of isomorphisms out of `D⁺_QCoh(𝒪_T)`: the comparison of [Stacks, Tag 0ATX] of the choice
for `f` and `h ∘ g`, followed by the one of the choice `E` for `g` and `h`, is the comparison of
the choice for `g ∘ f` and `h`, followed by the one of the choice for `f` and `g`, read through the
canonical comparisons of [Stacks, Tag 0AA0] of the compactifications of `g ∘ f` and of `f`. -/
theorem tripleCocycleIso :
    (tripleLeft E t).compIsoAPI ≪≫
        isoWhiskerRight
          (liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
            (isBoundedBelow_compactificationUpperShriek_obj E.outer)
            (fun K => isBoundedBelow_compactificationUpperShriek_obj E.inner
              ((upperShriekPlusAtModel E.base).obj K)) E.compIsoAPI)
          (compactificationUpperShriek f (tripleLeft E t).inner) =
      (tripleRight E t).compIsoAPI ≪≫
        isoWhiskerLeft (upperShriekPlusAtModel E.base)
          (compactificationUpperShriekIso (f ≫ g) (tripleRight E t).inner
            (tripleInner E t).outer) ≪≫
        isoWhiskerLeft (upperShriekPlusAtModel E.base) ((tripleInner E t).compIsoAPI ≪≫
          isoWhiskerLeft (upperShriekPlusAtModel E.inner)
            (compactificationUpperShriekIso f (tripleInner E t).inner (tripleLeft E t).inner)) :=
  assembleIso (isBoundedBelowQuasiCoherentAtModel T.left)
    (isBoundedBelowQuasiCoherentAtModel Z.left) (isBoundedBelowQuasiCoherentAtModel Y.left)
    (K := tw ((tripleLeft E t).top.toBase ≫ (tripleLeft E t).base.toBase))
    (iX := pb (tripleLeft E t).topImm) (BC := tw (tripleLeft E t).base.toBase)
    (iY := pb (tripleLeft E t).baseImm) (qU' := tw (tripleInner E t).innerSnd)
    (iU' := pb (tripleInner E t).innerImmersion) (qU := tw (tripleLeft E t).innerSnd)
    (iU := pb (tripleLeft E t).innerImmersion) (c := tw E.base.toBase) (iZ := pb E.baseImm)
    (qW := tw E.innerSnd) (iW := pb E.innerImmersion) (qV := tw (tripleRight E t).innerSnd)
    (iV := pb (tripleRight E t).innerImmersion)
    (RQ := tw ((tripleInner E t).top.toBase ≫ (tripleInner E t).base.toBase))
    (tripleRowMap E t) (tripleLeft E t).compMap E.compMap (tripleRight E t).compMap
    (whiskerRight (congrN (tripleMap_snd E t).symm).hom (pb (tripleRight E t).innerImmersion))
    (tripleInner E t).compMap (tripleAlphaA E t) (tripleAlphaE E t) (tripleAlphaD E)
    (tripleNat E t) (triplePsi E t) (tripleAlphaE_one E t) (tripleAlphaD_one E)
    (isBoundedBelow_compactificationUpperShriek_obj E.outer)
    (isBoundedBelow_compactificationUpperShriek_obj E.base)
    (isBoundedBelow_compactificationUpperShriek_obj E.inner)
    (fun K => isBoundedBelow_compactificationUpperShriek_obj E.inner
      ((upperShriekPlusAtModel E.base).obj K))
    (tripleLeft E t).compIsoAPI E.compIsoAPI (tripleRight E t).compIsoAPI
    (compactificationUpperShriekIso (f ≫ g) (tripleRight E t).inner (tripleInner E t).outer)
    (tripleInner E t).compIsoAPI
    (compactificationUpperShriekIso f (tripleInner E t).inner (tripleLeft E t).inner)
    rfl rfl rfl (tripleTransport E t) rfl (tripleAlphaA_hom' E t)

/-- Changing the first compactification in the choice for `D` composes with the comparison of
[Stacks, Tag 0AA0]. -/
private theorem upperShriekCompIsoAtModel_choice_trans {A B C : FTS S} {a : A ⟶ B} {b : B ⟶ C}
    (D : CompositionData a b) (j' : CompactificationOf (Over.mk a.left)) :
    upperShriekCompIsoAtModel D.outer j' D.base = D.compIsoAPI ≪≫
      isoWhiskerLeft (upperShriekPlusAtModel D.base)
        (compactificationUpperShriekIso a D.inner j') :=
  (upperShriekCompIsoAtModel_change_inner _ _ _ _).trans
    (congrArg (· ≪≫ _) (upperShriekCompIsoAtModel_choice D))

/-- **The cocycle identity of [Stacks, Tag 0ATY] for the triple of compactifications**, for the
canonical isomorphisms `Stacks.Duality.upperShriekCompIsoAtModel` of [Stacks, Tag 0ATX]. -/
theorem tripleCocycle_upperShriekCompIso :
    upperShriekCompIsoAtModel (tripleLeft E t).outer (tripleLeft E t).inner E.outer ≪≫
        isoWhiskerRight
          (liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
            (isBoundedBelow_compactificationUpperShriek_obj E.outer)
            (fun K => isBoundedBelow_compactificationUpperShriek_obj E.inner
              ((upperShriekPlusAtModel E.base).obj K))
            (upperShriekCompIsoAtModel E.outer E.inner E.base))
          (compactificationUpperShriek f (tripleLeft E t).inner) =
      upperShriekCompIsoAtModel (f := f ≫ g) (g := h) (tripleLeft E t).outer (tripleInner E t).outer
          E.base ≪≫
        isoWhiskerLeft (upperShriekPlusAtModel E.base)
          (upperShriekCompIsoAtModel (tripleInner E t).outer (tripleLeft E t).inner E.inner) := by
  have e1 : upperShriekCompIsoAtModel (tripleLeft E t).outer (tripleLeft E t).inner E.outer =
      _ := upperShriekCompIsoAtModel_choice (tripleLeft E t)
  have e2 : upperShriekCompIsoAtModel E.outer E.inner E.base = _ :=
    upperShriekCompIsoAtModel_choice E
  have e3 : upperShriekCompIsoAtModel (f := f ≫ g) (g := h) (tripleLeft E t).outer
      (tripleInner E t).outer E.base = _ :=
    upperShriekCompIsoAtModel_choice_trans (tripleRight E t) _
  have e4 : upperShriekCompIsoAtModel (tripleInner E t).outer (tripleLeft E t).inner E.inner =
      _ := upperShriekCompIsoAtModel_choice_trans (tripleInner E t) _
  rw [e1, e2, e3, e4]
  exact (tripleCocycleIso E t).trans (Iso.trans_assoc _ _ _).symm

end CompositionData

end Triple

/-- The isomorphism `(h ∘ g)^! ≅ g^! ∘ h^!` of [Stacks, Tag 0ATX] read in `D⁺_QCoh(𝒪_Y)`. -/
abbrev upperShriekCompIsoAtModelPlus {Y Z T : FTS S} {g : Y ⟶ Z} {h : Z ⟶ T}
    (k : CompactificationOf (Over.mk (g ≫ h).left)) (j : CompactificationOf (Over.mk g.left))
    (i : CompactificationOf (Over.mk h.left)) :
    upperShriekPlusAtModel k ≅ upperShriekPlusAtModel i ⋙ upperShriekPlusAtModel j :=
  liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
    (isBoundedBelow_compactificationUpperShriek_obj k)
    (fun K => isBoundedBelow_compactificationUpperShriek_obj j ((upperShriekPlusAtModel i).obj K))
    (upperShriekCompIsoAtModel k j i)

/-- `Stacks.Duality.upperShriekCompIsoAtModel_naturality` read in `D⁺_QCoh(𝒪_Y)`. -/
theorem upperShriekCompIsoAtModelPlus_naturality {Y Z T : FTS S} {g : Y ⟶ Z} {h : Z ⟶ T}
    (k k' : CompactificationOf (Over.mk (g ≫ h).left)) (j j' : CompactificationOf (Over.mk g.left))
    (i i' : CompactificationOf (Over.mk h.left)) :
    basePlusIsoAPI k k' ≪≫ upperShriekCompIsoAtModelPlus k' j' i' =
      upperShriekCompIsoAtModelPlus k j i ≪≫ NatIso.hcomp (basePlusIsoAPI i i')
          (basePlusIsoAPI j j') := by
  have n := congrArg (liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
    (isBoundedBelow_compactificationUpperShriek_obj k)
    (fun K => isBoundedBelow_compactificationUpperShriek_obj j'
        ((upperShriekPlusAtModel i').obj K)))
    (upperShriekCompIsoAtModel_naturality k k' j j' i i')
  rw [liftIsoOf_trans _ _ (isBoundedBelow_compactificationUpperShriek_obj k'),
    liftIsoOf_trans _ _
      (fun K => isBoundedBelow_compactificationUpperShriek_obj j
          ((upperShriekPlusAtModel i).obj K)),
    liftIsoOf_hcomp _ _ _ (isBoundedBelow_compactificationUpperShriek_obj j)
      (isBoundedBelow_compactificationUpperShriek_obj j')] at n
  exact n

/-- **[Stacks, Tag 0ATY], the cocycle identity, for arbitrary compactifications**: for composable
morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ T` of `FTS S` and compactifications of `h ∘ g ∘ f`,
`f`, `h ∘ g`, `g`, `h` and `g ∘ f`, the canonical isomorphisms of [Stacks, Tag 0ATX] satisfy
`γ_{A+B}` followed by `γ_C` equals `γ_{B+C}` followed by `γ_A`, as isomorphisms of functors out of
`D⁺_QCoh(𝒪_T)`. The proof is the source's: a choice of compactifications `Z̄` of `Z` over `T`,
`Ȳ` of `Y` over `Z̄` and `X̄` of `X` over `Ȳ` (More on Flatness, Theorem 0F41 and Lemma 0A9Z),
the chase `Stacks.Duality.CompositionData.tripleCocycleIso`, and the canonical comparisons of
[Stacks, Tag 0AA0] to pass to arbitrary compactifications. -/
theorem upperShriekCompIsoAtModel_cocycle {X Y Z T : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
    (kfgh : CompactificationOf (Over.mk (f ≫ g ≫ h).left))
    (kf : CompactificationOf (Over.mk f.left)) (kgh : CompactificationOf (Over.mk (g ≫ h).left))
    (kg : CompactificationOf (Over.mk g.left)) (kh : CompactificationOf (Over.mk h.left))
    (kfg : CompactificationOf (Over.mk (f ≫ g).left)) :
    upperShriekCompIsoAtModel kfgh kf kgh ≪≫
        isoWhiskerRight (upperShriekCompIsoAtModelPlus kgh kg kh)
            (compactificationUpperShriek f kf) =
      upperShriekCompIsoAtModel (f := f ≫ g) (g := h) kfgh kfg kh ≪≫
        isoWhiskerLeft (upperShriekPlusAtModel kh) (upperShriekCompIsoAtModel kfg kf kg) := by
  let E : CompositionData g h := CompositionData.ofCompactifications kgh kh
  let t : CompactificationOf (Over.mk (f.left ≫ E.top.immersion)) :=
    Classical.choice (CompositionData.exists_top kfgh E.outer)
  exact cocycleTransport
    (compactificationUpperShriekIso (f ≫ g ≫ h) (E.tripleLeft t).outer kfgh)
    (basePlusIsoAPI E.base kh) (basePlusIsoAPI E.inner kg)
    (compactificationUpperShriekIso f (E.tripleLeft t).inner kf)
    (basePlusIsoAPI E.outer kgh)
    (compactificationUpperShriekIso (f ≫ g) (E.tripleInner t).outer kfg)
    _ _ (upperShriekCompIsoAtModel_naturality (E.tripleLeft t).outer kfgh (E.tripleLeft t).inner kf
      E.outer kgh)
    _ _ (upperShriekCompIsoAtModelPlus_naturality E.outer kgh E.inner kg E.base kh)
    _ _ (upperShriekCompIsoAtModel_naturality (f := f ≫ g) (g := h) (E.tripleLeft t).outer kfgh
      (E.tripleInner t).outer kfg E.base kh)
    _ _ (upperShriekCompIsoAtModel_naturality (E.tripleInner t).outer kfg (E.tripleLeft t).inner kf
      E.inner kg)
    (CompositionData.tripleCocycle_upperShriekCompIso E t)

end Stacks.Duality

end
