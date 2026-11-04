module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactification
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessPresentationToType
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# The reduction to a flat base in the proof of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack to a
quasi-compact and quasi-separated algebraic space, and `V ⊆ Y` a quasi-compact open subspace over
which `𝒳` is a gerbe. The second reduction of the proof of [Stacks, Tag 0CQ7] reads: "Using
Lemma 0CQ4 (and 06QI to see that a gerbe is flat and locally of finite presentation) we reduce to
the case where `f` is flat and of finite presentation."

Lemma 0CQ4 produces a `V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳 ×_Y Y'`
containing every object over `V' = b⁻¹V`, flat and of finite presentation over `Y'`. The pair
`(𝒳' ⟶ Y', V')` again satisfies the hypotheses of Stacks 0CQ7: `𝒳' ⟶ 𝒳` is proper, `𝒳' ⟶ Y'` is
separated of finite type, `Y'` is quasi-compact and quasi-separated, `b` restricts to an
isomorphism `V' ≅ V`, and `𝒳'_{V'}` is a gerbe over `V'` because it is all of `(𝒳 ×_Y Y')_{V'}`,
which is the base change of the gerbe `𝒳_V ⟶ V` along `V' ⟶ V`. The initial remark of the proof
then brings the conclusion for `(𝒳' ⟶ Y', V')` down to `(f, V)`.

The reduction takes the conclusion of Lemma 0CQ4 as the hypothesis `h0CQ4`, and the flat case of
Stacks 0CQ7 as the hypothesis `hflat`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.fullSubcategorySndEquivalence`: when every object of
  `𝒳 ×_𝒮 𝒴` has its `𝒴`-component in a full subcategory `𝒴_P`, the 2-fibre product is isomorphic
  to `𝒳 ×_𝒮 𝒴_P`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_flat_case`: the
  reduction of Stacks 0CQ7 to the case of a flat 1-morphism of finite presentation.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- The 2-fibre product `𝒳 ×_𝒮 𝒴` maps to `𝒳 ×_𝒮 𝒴_P` when the `𝒴`-component of every object
lies in the full subcategory `𝒴_P`: tag that component with its membership proof. -/
def toFullSubcategorySnd (P : ObjectProperty 𝒴)
    (h : ∀ d : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G, P d.y) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤
      TwoFibreProductOver p𝒳 (P.ι ⋙ p𝒴) p𝒮 F (P.ι ⋙ G) where
  obj d :=
    { base := d.base
      x := d.x
      y := ⟨d.y, h d⟩
      hx := d.hx
      hy := d.hy
      iso := d.iso
      vertical := d.vertical }
  map φ :=
    { hbase := φ.hbase
      a := φ.a
      b := ObjectProperty.homMk φ.b
      ha := φ.ha
      hb := by
        rw [Functor.isHomLift_comp_iff, ObjectProperty.ι_map, ObjectProperty.homMk_hom]
        exact φ.hb
      w := φ.w }
  map_id _ := Hom.ext' rfl (ObjectProperty.hom_ext _ (by simp))
  map_comp _ _ := Hom.ext' rfl (ObjectProperty.hom_ext _ (by simp))

/-- The 2-fibre product `𝒳 ×_𝒮 𝒴_P` with a full subcategory `𝒴_P` maps to `𝒳 ×_𝒮 𝒴`: forget the
membership proof of the `𝒴`-component. -/
def ofFullSubcategorySnd (P : ObjectProperty 𝒴) :
    TwoFibreProductOver p𝒳 (P.ι ⋙ p𝒴) p𝒮 F (P.ι ⋙ G) ⥤
      TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G where
  obj d :=
    { base := d.base
      x := d.x
      y := d.y.obj
      hx := d.hx
      hy := d.hy
      iso := d.iso
      vertical := d.vertical }
  map φ :=
    { hbase := φ.hbase
      a := φ.a
      b := φ.b.hom
      ha := φ.ha
      hb := by simpa only [Functor.isHomLift_comp_iff, ObjectProperty.ι_map] using φ.hb
      w := φ.w }
  map_id _ := Hom.ext' rfl (by simp)
  map_comp _ _ := Hom.ext' rfl (by simp)

/-- **A 2-fibre product all of whose objects have their second component in a full subcategory
is the 2-fibre product with that full subcategory.** If the `𝒴`-component of every object of
`𝒳 ×_𝒮 𝒴` satisfies `P`, then `𝒳 ×_𝒮 𝒴` is equivalent (indeed isomorphic) to `𝒳 ×_𝒮 𝒴_P`, by
tagging the `𝒴`-component with its membership proof. -/
def fullSubcategorySndEquivalence (P : ObjectProperty 𝒴)
    (h : ∀ d : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G, P d.y) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ≌
      TwoFibreProductOver p𝒳 (P.ι ⋙ p𝒴) p𝒮 F (P.ι ⋙ G) :=
  Equivalence.mk (toFullSubcategorySnd P h) (ofFullSubcategorySnd P) (Iso.refl _) (Iso.refl _)

end CategoryTheory.TwoFibreProductOver

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A `V`-admissible blowup `b : Y' ⟶ Y` restricts to an isomorphism `b⁻¹V ≅ V`
(Stacks 085T). -/
private theorem isIso_fromPreimage_of_isAdmissibleBlowup_flatCase
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y} {V : Subfunctor Y}
    {hV : Space.IsOpenSubspace B S hS V}
    {Y' : AlgebraicSpaces B S hS} {b : Y' ⟶ ⟨Y, hY⟩}
    (hb : Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b) : IsIso (V.fromPreimage b.hom) := by
  obtain ⟨Z, -, hdisj, hbl⟩ := hb
  have hVU : V ≤ (Space.openComplementOfClosedSubspace B S hS ⟨Y, hY⟩ Z).1 := by
    refine Space.le_of_range_pointsMap_ι_subset B S hS
      (Space.openComplementOfClosedSubspace B S hS ⟨Y, hY⟩ Z).2 ?_
    show Space.subspacePointSet B S hS Y V ⊆ Space.subspacePointSet B S hS Y _
    rw [Space.subspacePointSet_openComplement]
    exact hdisj.subset_compl_right
  exact Space.isIso_fromPreimage_of_le b.hom hVU (Space.isIso_fromPreimage_openComplement hbl)

/-- If `b` restricts to an isomorphism `b⁻¹V ≅ V`, every point of `V` is the image under `b` of a
point of `b⁻¹V`. -/
private theorem range_pointsMap_ι_subset_image_of_isIso_fromPreimage
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : Y' ⟶ Y) (V : Subfunctor Y)
    [IsIso (V.fromPreimage b)] :
    Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Space.pointsMap B S hS Y' b '' Set.range (Space.pointsMap B S hS _ (V.preimage b).ι) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨Space.pointsMap B S hS _ (V.preimage b).ι
    (Space.pointsMap B S hS V.toFunctor (inv (V.fromPreimage b)) v), ⟨_, rfl⟩, ?_⟩
  rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι,
    IsIso.inv_hom_id_assoc]

/-- **The restriction of a closed substack to the inverse image of a gerbe locus is a gerbe.** Let
`𝒳_V ⟶ V` be a gerbe, `b : Y' ⟶ Y` a morphism of algebraic spaces and `𝒳' ⊆ 𝒳 ×_Y Y'` a substack
containing every object over `V' = b⁻¹V`. Then `𝒳'_{V'} ⟶ V'` is a gerbe: it is all of
`(𝒳 ×_Y Y')_{V'}`, the base change of `𝒳_V ⟶ V` along `V' ⟶ V` (Stacks 06QE). -/
private theorem isGerbeOver_fullSubcategory_preimage
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ ⟨Y, hY⟩)
    (hV' : Space.IsOpenSubspace B S hS (V.preimage b.hom))
    (P : ObjectProperty (twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj)
    (hPV : ∀ x, ((twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
        x).fiber.as ∈ (V.preimage b.hom).obj (Opposite.op ((twoFibreProductSquare B S hS
          (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj x).base) →
      P x)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P)) :
    IsGerbeOver B S hS (twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι)
      (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
        (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst)).fst := by
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let V' : Subfunctor Y'.1 := V.preimage b.hom
  let c : V'.toFunctor ⟶ V.toFunctor := V.fromPreimage b.hom
  let GV := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  have hGV : Bicategory.IsTwoFibreProduct GV := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let W := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 c) GV.fst
  have hW : Bicategory.IsTwoFibreProduct W :=
    isTwoFibreProduct_twoFibreProductSquare B S hS _ GV.fst
  let T := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι)
    Q.fst
  have hT : Bicategory.IsTwoFibreProduct T :=
    isTwoFibreProduct_twoFibreProductSquare B S hS _ Q.fst
  have heq : algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 c ≫
        algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι =
      algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι ≫
        algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom := by
    rw [← algebraicSpaceStackMap_comp, ← algebraicSpaceStackMap_comp,
      Subfunctor.fromPreimage_ι V b.hom]
  have hTg : IsGerbeOver B S hS T.fst :=
    isGerbeOver_snd_of_isGerbeOver_snd B S hS
      (Bicategory.isTwoFibreProduct_reindexSnd (eqToIso heq)
        (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_pasteFst GV hGV W hW)))
      (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_pasteFst Q hQ T hT))
      (isGerbeOver_of_isTwoFibreProduct B S hS W.swap (Bicategory.isTwoFibreProduct_swap hW) hG)
  have hTP : ∀ d : T.pt.val.val.obj, P (T.snd.hom.hom.obj d) := by
    rintro ⟨U, x, y, hx, hy, e, he⟩
    refine hPV _ ?_
    have h : (Q.fst.hom.hom.obj y).fiber.as = Y'.1.map e.inv.base.op x.fiber.as.1 :=
      Discrete.eq_of_hom e.inv.fiber
    show (Q.fst.hom.hom.obj y).fiber.as ∈ V'.obj (op (Q.fst.hom.hom.obj y).base)
    rw [h]
    exact V'.map e.inv.base.op x.fiber.as.2
  let E := TwoFibreProductOver.fullSubcategorySndEquivalence P hTP
  exact isGerbeOver_of_isEquivalence_comp B S hS
    (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨E.functor, rfl⟩))
    _ T.fst E.isEquivalence_functor (Iso.refl _) hTg

/-- **The reduction of Stacks 0CQ7 to a flat 1-morphism of finite presentation.** Let
`f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack to a quasi-compact
quasi-separated algebraic space, and `V ⊆ Y` a quasi-compact open subspace with `𝒳_V` a gerbe over
`V`. Given the conclusion of Stacks 0CQ4 (`h0CQ4`) and the conclusion of Stacks 0CQ7 for flat
1-morphisms of finite presentation (`hflat`), the conclusion of Stacks 0CQ7 holds for `(f, V)`.

This is the second reduction of the proof of [Stacks, Tag 0CQ7]. The gerbe `𝒳_V ⟶ V` is flat and
locally of finite presentation (Stacks 06QI), so Stacks 0CQ4 gives a `V`-admissible blowup
`b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳 ×_Y Y'` containing every object over `V' = b⁻¹V`,
flat and of finite presentation over `Y'`. The projection `𝒳' ⟶ 𝒳` is proper (a closed immersion
followed by a base change of the proper `b`), `𝒳' ⟶ Y'` is separated of finite type, `Y'` is
quasi-compact and quasi-separated (it is proper over `Y`), and `b` restricts to an isomorphism
`V' ≅ V` because `V` misses the centre (Stacks 085T). Finally `𝒳'_{V'}` is a gerbe over `V'`: it
is isomorphic to `(𝒳 ×_Y Y')_{V'}`, every object of which lies in `𝒳'`, and that is a base change
of `𝒳_V ⟶ V` along `V' ⟶ V` (pasting of 2-fibre products, Stacks 06QE). The initial remark,
`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_proper`, then brings the
conclusion for `(𝒳' ⟶ Y', V')` down to `(f, V)`. -/
theorem hasProperCompactifiableCover_of_flat_case
    (h0CQ4 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      IsFiniteType B S hS f → IsQuasiSeparated B S hS f →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsFlat B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      IsLocallyOfFinitePresentation B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ ⟨Y, hY⟩),
        Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b ∧
        ∃ P : ObjectProperty (twoFibreProductSquare B S hS
            (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj,
          IsClosedSubstack _ P ∧
          (∀ x, ((twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                x).fiber.as ∈ (V.preimage b.hom).obj (Opposite.op ((twoFibreProductSquare B S hS
                  (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                    x).base) →
            P x) ∧
          ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P),
            IsFlat B S hS (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) ∧
            IsFinitePresentation B S hS (fullSubcategoryInclusion _ P hP ≫
              (twoFibreProductSquare B S hS
                (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst))
    (hflat : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSeparated B S hS f → IsFiniteType B S hS f → IsFlat B S hS f →
      IsFinitePresentation B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      HasProperCompactifiableCover.{u, w} B S hS hY f V)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  -- Stacks 06QI: the gerbe `𝒳_V ⟶ V` is flat and locally of finite presentation.
  obtain ⟨hGfl, hGlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS _ hG
  -- Stacks 0CQ4.
  obtain ⟨Y', b, hb, P, ⟨-, hP, hci⟩, hPV, hPfl⟩ := h0CQ4 Y hY 𝒳 f V hV hYqc hYqs hft
    (isQuasiSeparated_of_isSeparated B S hS hsep) hVqc hGfl hGlfp
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let ι := fullSubcategoryInclusion Q.pt P hP
  let f' : fullSubcategoryAlgebraicStack Q.pt P hP ⟶
    algebraicSpaceStack.{u, w} B S hS Y'.1 Y'.2 := ι ≫ Q.fst
  have hbp : Space.IsProper B S hS b.hom := Space.IsAdmissibleBlowup.isProper B S hS hb
  have ha : IsProper B S hS (ι ≫ Q.snd) :=
    isProper_comp B S hS ι Q.snd (isProper_of_isClosedImmersion B S hS ι hci)
      (isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ)
        ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS Y'.2 hY b.hom).2 hbp))
  have hf'sep : IsSeparated B S hS f' :=
    isSeparated_comp B S hS ι Q.fst (isSeparated_of_isClosedImmersion B S hS ι hci)
      (isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ) hsep)
  obtain ⟨hf'fl, hf'fp⟩ := hPfl hP
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y'.1 :=
    Space.isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc b.hom hbp.2.1.2
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1 :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal Y'.2 hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hbp.1)
  -- `b` restricts to an isomorphism `V' = b⁻¹V ≅ V`, `V` missing the centre (Stacks 085T).
  let V' : Subfunctor Y'.1 := V.preimage b.hom
  have hV' : Space.IsOpenSubspace B S hS V' :=
    Space.isOpenSubspace_preimage B S hS b.hom V hY Y'.2 hV
  have := isIso_fromPreimage_of_isAdmissibleBlowup_flatCase B S hS hb
  exact HasProperCompactifiableCover.of_proper B S hS hY Y'.2 f f' b.hom hbp (ι ≫ Q.snd) ha
    (Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso ι Q.iso.symm ≪≫
      (Bicategory.associator _ _ _).symm) V V'
    (range_pointsMap_ι_subset_image_of_isIso_fromPreimage B S hS b.hom V)
    (hflat Y'.1 Y'.2 _ f' V' hV' hf'sep (isFiniteType_of_isFinitePresentation B S hS f' hf'fp)
      hf'fl hf'fp hY'qc hY'qs (hVqc.of_iso B S hS (asIso (V.fromPreimage b.hom)).symm)
      (isGerbeOver_fullSubcategory_preimage B S hS hY f V hV hG Y' b hV' P hPV hP))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
