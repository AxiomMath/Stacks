module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKBaseCase
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductRestrict
public import StacksFrontier.CategoryTheory.Functor.KanExtension.CommaSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.NaturalComplementComparison

/-!
# The displayed formula (07MK) computing `Rf_{cris, *}`

[Stacks, Tag 07MJ] states, without proof, that for an object `(U', T', δ')` of `Cris(X'/S')`,
with `U = X ×_{X'} U'` and `T = S ×_{S'} T'`,

`(Rf_{cris, *}F)_{T'} = R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`.

This file proves it, as an isomorphism of functors `Ab(Cris(X/S)) ⥤ D⁺(Ab(T'_Zar))` of the two
sides `Crystalline.GlobalCrystallineSituation.SmallSite.leftSide07MK` and `...rightSide07MK`.

## The proof

*The underived formula.*  On presheaves both sides of `(f_{cris, *}F)_{T'} ≅
(T ⟶ T')_*(τ_{U/T, *}F_U)` are a right Kan extension followed by a restriction: along
`Cris(X/S) ⥤ CRIS(X'/S')` and then along `W ↦ (U', T', δ')|_W` on the left, along
`Cris(U/T) ⥤ U_Zar` and then along `W ↦ (U ⟶ T')⁻¹W` on the right.  The comma square is Guitart
exact (`CategoryTheory.TwoSquare.ranCommaIso`), so each side is one right Kan extension along the
first projection of a comma category over `T'_Zar`.  The two comma categories are equivalent over
`T'_Zar` (`rightToLeftIndexEquivalence07MK`): an object of `Cris(U/T)` lying over `W` is the same
as an object of `Cris(X/S)` with a morphism to `(U', T', δ')|_W` over `S ⟶ S'`.  This is the
identification `Cris(U/T) ≌ Cris(X/S) ↓ (U', T', δ')` of
`Crystalline.GlobalCrystallineSituation.pullbackCrystallineCommaEquivalence` together with the
universal property of the restriction to an open; it is how the hint of the source, that
`Cris(U/T)` is the localization of `Cris(X/S)` at `f_cris^{-1}h_{(U', T', δ')}`, is used.

*The derived formula.*  Restriction `G ↦ G_{T'}` is exact, so `(Rf_{cris, *}F)_{T'}` is the
derived functor of `F ↦ (f_{cris, *}F)_{T'}`.  The pullback `F ↦ F_U` is exact and preserves
injectives and `τ_{U/T, *}` preserves injectives, so `R(T ⟶ T')_*(Rτ_{U/T, *}F_U)` is the derived
functor of `F ↦ (T ⟶ T')_*(τ_{U/T, *}F_U)` applied to `F[0]` ([Stacks, Tag 015M]).  Isomorphic
functors have isomorphic derived functors.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.formulaBase07MK`: the underived formula.
* `Crystalline.GlobalCrystallineSituation.SmallSite.formula07MK`: **the displayed equation (07MK)
  at one object `(U', T', δ')`.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.computes07MK`: (07MK) for every object of
  `Cris(X'/S')`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

include hf

/-- The preimage functor `T'_Zar ⥤ U_Zar` along `U ⟶ T ⟶ T'`. -/
abbrev pullbackOpensMap :
    A'.obj.thickening.target.scheme.Opens ⥤ (pullbackSituation S S' fS fX hf A').X.Opens :=
  Opens.map (pullback.snd fS A'.obj.toBase).hom.base ⋙
    Opens.map (sourceToBase (pullbackSituation S S' fS fX hf A')).base

/-- The index category of the right-hand side. -/
abbrev rightIndex07MK : Type _ :=
  Comma (pullbackOpensMap S S' fS fX hf A').op
    (forgetToOpens (pullbackSituation S S' fS fX hf A')).op

/-- The index category of the left-hand side. -/
abbrev leftIndex07MK : Type _ :=
  Comma (CrystallineThickening.restrictOpenFunctor A' ⋙ CrystallineThickening.ι S').op
    (crisToBigOp S S' fS fX hf)

/-- The topological criterion. -/
theorem range_pullbackCommaProj_subset
    (D : CrystallineThickening (pullbackSituation S S' fS fX hf A'))
    (W : A'.obj.thickening.target.scheme.Opens)
    (h : (forgetToOpens (pullbackSituation S S' fS fX hf A')).obj D ≤
      (pullbackOpensMap S S' fS fX hf A').obj W) :
    Set.range (pullbackCommaProj S S' fS fX hf A' D.obj).targetHom.hom.base ⊆
      (W : Set A'.obj.thickening.target.scheme) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨v, rfl⟩ := D.obj.thickening.isThickening.2 z
  have hv := h ⟨v, rfl⟩
  have e := congrArg (fun φ => φ.base v) D.obj.over_base
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  change (pullback.snd fS A'.obj.toBase).hom.base (D.obj.toBase.hom.base _) ∈ W
  rw [e]
  exact hv

/-- The converse of `range_pullbackCommaProj_subset`. -/
theorem forgetToOpens_le_of_range_subset
    (D : CrystallineThickening (pullbackSituation S S' fS fX hf A'))
    (W : A'.obj.thickening.target.scheme.Opens)
    (h : Set.range (pullbackCommaProj S S' fS fX hf A' D.obj).targetHom.hom.base ⊆
      (W : Set A'.obj.thickening.target.scheme)) :
    (forgetToOpens (pullbackSituation S S' fS fX hf A')).obj D ≤
      (pullbackOpensMap S S' fS fX hf A').obj W := by
  rintro _ ⟨v, rfl⟩
  have e := congrArg (fun φ => φ.base v) D.obj.over_base
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  have hv := h ⟨D.obj.thickening.immersion v, rfl⟩
  change (pullback.snd fS A'.obj.toBase).hom.base (D.obj.toBase.hom.base _) ∈ W at hv
  rw [e] at hv
  exact hv

omit hf in
/-- A morphism into a restriction, followed by its structure morphism, lands in the open. -/
theorem range_comp_restrictOpenHom_subset {T : Thickening S'}
    (W : A'.obj.thickening.target.scheme.Opens) (f : T ⟶ A'.obj.restrictOpen W) :
    Set.range (f ≫ A'.obj.restrictOpenHom W).targetHom.hom.base ⊆
      (W : Set A'.obj.thickening.target.scheme) := by
  rintro _ ⟨z, rfl⟩
  change W.ι.base (f.targetHom.hom.base z) ∈ W
  exact (f.targetHom.hom.base z).2

/-- The factorization of the structure morphism to `(U', T', δ')` through the restriction. -/
def pullbackCommaLift (X : rightIndex07MK S S' fS fX hf A') :
    (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj X.right.unop) ⟶
      A'.obj.restrictOpen X.left.unop :=
  Thickening.restrictOpenLift (pullbackCommaProj S S' fS fX hf A' X.right.unop.obj) X.left.unop
    (range_pullbackCommaProj_subset S S' fS fX hf A' X.right.unop X.left.unop X.hom.unop.le)

/-- The factorization `pullbackCommaLift`, followed by the structure morphism of the restriction,
is the structure morphism `pullbackCommaProj` to `(U', T', δ')`. -/
@[reassoc]
theorem pullbackCommaLift_restrictOpenHom (X : rightIndex07MK S S' fS fX hf A') :
    pullbackCommaLift S S' fS fX hf A' X ≫ A'.obj.restrictOpenHom X.left.unop =
      pullbackCommaProj S S' fS fX hf A' X.right.unop.obj :=
  Thickening.restrictOpenLift_restrictOpenHom _ _ _

/-- `pullbackCommaLift` is natural in the object of the right index category. -/
theorem pullbackCommaLift_naturality {X Y : rightIndex07MK S S' fS fX hf A'} (f : X ⟶ Y) :
    pullbackCommaLift S S' fS fX hf A' Y ≫ A'.obj.restrictOpenLE f.left.unop.le =
      (crisToBig S S' fS fX hf).map ((pullbackSmallChangeBase S S' fS fX hf A').map f.right.unop) ≫
        pullbackCommaLift S S' fS fX hf A' X := by
  rw [← cancel_mono (A'.obj.restrictOpenHom X.left.unop), Category.assoc,
    Thickening.restrictOpenLE_restrictOpenHom, pullbackCommaLift_restrictOpenHom, Category.assoc,
    pullbackCommaLift_restrictOpenHom]
  exact (CostructuredArrow.w ((pullbackCrisToComma S S' fS fX hf A').map f.right.unop)).symm

/-- The comparison functor of index categories. -/
@[simps]
def rightToLeftIndex07MK : rightIndex07MK S S' fS fX hf A' ⥤ leftIndex07MK S S' fS fX hf A' where
  obj X := ⟨X.left, op ((pullbackSmallChangeBase S S' fS fX hf A').obj X.right.unop),
    (pullbackCommaLift S S' fS fX hf A' X).op⟩
  map {X Y} f := ⟨f.left, ((pullbackSmallChangeBase S S' fS fX hf A').map f.right.unop).op,
    Quiver.Hom.unop_inj (pullbackCommaLift_naturality S S' fS fX hf A' f)⟩
  map_id X := by apply Comma.hom_ext <;> simp
  map_comp f g := by apply Comma.hom_ext <;> simp

/-- Change of divided power base `Cris(U/T) ⥤ Cris(X/S)` is faithful. -/
theorem pullbackSmallChangeBase_map_injective
    {D₁ D₂ : CrystallineThickening (pullbackSituation S S' fS fX hf A')} {a b : D₁ ⟶ D₂}
    (h : (pullbackSmallChangeBase S S' fS fX hf A').map a =
      (pullbackSmallChangeBase S S' fS fX hf A').map b) : a = b :=
  (pullbackCrisToComma S S' fS fX hf A').map_injective (CostructuredArrow.hom_ext _ _ h)

/-- The comparison of index categories is faithful. -/
instance faithful_rightToLeftIndex07MK : (rightToLeftIndex07MK S S' fS fX hf A').Faithful where
  map_injective {X Y} {a b} h := by
    have hl := congrArg CommaMorphism.left h
    have hr := congrArg (fun m => m.right.unop) h
    refine Comma.hom_ext _ _ hl (Quiver.Hom.unop_inj ?_)
    exact pullbackSmallChangeBase_map_injective S S' fS fX hf A' hr

/-- The comma condition of `Cris(U/T)` from a factorization through restrictions. -/
theorem comp_pullbackCommaProj_of_lift
    {D₁ D₂ : CrystallineThickening (pullbackSituation S S' fS fX hf A')}
    {W W' : A'.obj.thickening.target.scheme.Opens} (hW : W ≤ W')
    (x : (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj D₂) ⟶
      (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj D₁))
    (l₁ : (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj D₁) ⟶
      A'.obj.restrictOpen W')
    (l₂ : (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj D₂) ⟶
      A'.obj.restrictOpen W)
    (h : l₂ ≫ A'.obj.restrictOpenLE hW = x ≫ l₁)
    (h₁ : l₁ ≫ A'.obj.restrictOpenHom W' = pullbackCommaProj S S' fS fX hf A' D₁.obj)
    (h₂ : l₂ ≫ A'.obj.restrictOpenHom W = pullbackCommaProj S S' fS fX hf A' D₂.obj) :
    x ≫ pullbackCommaProj S S' fS fX hf A' D₁.obj = pullbackCommaProj S S' fS fX hf A' D₂.obj := by
  rw [← h₁, ← Category.assoc, ← h, Category.assoc, Thickening.restrictOpenLE_restrictOpenHom, h₂]

/-- The comparison of index categories is full, by fullness of
`Crystalline.GlobalCrystallineSituation.pullbackCrisToComma`. -/
instance full_rightToLeftIndex07MK : (rightToLeftIndex07MK S S' fS fX hf A').Full where
  map_surjective {X Y} m := by
    have hm : (crisToBig S S' fS fX hf).map m.right.unop ≫
        pullbackCommaProj S S' fS fX hf A' X.right.unop.obj =
          pullbackCommaProj S S' fS fX hf A' Y.right.unop.obj :=
      comp_pullbackCommaProj_of_lift S S' fS fX hf A' m.left.unop.le _ _ _
        (congrArg Quiver.Hom.unop m.w) (pullbackCommaLift_restrictOpenHom S S' fS fX hf A' X)
        (pullbackCommaLift_restrictOpenHom S S' fS fX hf A' Y)
    let g := (pullbackCrisToComma S S' fS fX hf A').preimage
      (CostructuredArrow.homMk m.right.unop hm)
    have hg : (pullbackSmallChangeBase S S' fS fX hf A').map g = m.right.unop :=
      congrArg CommaMorphism.left ((pullbackCrisToComma S S' fS fX hf A').map_preimage _)
    refine ⟨⟨m.left, g.op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩, ?_⟩
    exact Comma.hom_ext _ _ rfl (Quiver.Hom.unop_inj hg)

omit hf in
/-- A morphism into a restriction, after any morphism and followed by the structure morphism of the
restriction, lands in the open. -/
theorem range_comp_comp_restrictOpenHom_subset {T T₀ : Thickening S'}
    (W : A'.obj.thickening.target.scheme.Opens) (g : T₀ ⟶ T) (f : T ⟶ A'.obj.restrictOpen W) :
    Set.range (g ≫ f ≫ A'.obj.restrictOpenHom W).targetHom.hom.base ⊆
      (W : Set A'.obj.thickening.target.scheme) := by
  rintro _ ⟨z, rfl⟩
  change W.ι.base ((g ≫ f).targetHom.hom.base z) ∈ W
  exact ((g ≫ f).targetHom.hom.base z).2

/-- The comma condition of `Comma.isoMk` in the proof of essential surjectivity. -/
theorem eq_crisToBig_map_inv_comp_of_restrictOpenHom
    {D : CrystallineThickening (pullbackSituation S S' fS fX hf A')} {B : CrystallineThickening S}
    (W : A'.obj.thickening.target.scheme.Opens)
    (y : (crisToBig S S' fS fX hf).obj B ⟶ A'.obj.restrictOpen W)
    (eL : (pullbackSmallChangeBase S S' fS fX hf A').obj D ≅ B)
    (we : (crisToBig S S' fS fX hf).map eL.hom ≫ y ≫ A'.obj.restrictOpenHom W =
      pullbackCommaProj S S' fS fX hf A' D.obj)
    (l : (crisToBig S S' fS fX hf).obj ((pullbackSmallChangeBase S S' fS fX hf A').obj D) ⟶
      A'.obj.restrictOpen W)
    (hl : l ≫ A'.obj.restrictOpenHom W = pullbackCommaProj S S' fS fX hf A' D.obj) :
    y = (crisToBig S S' fS fX hf).map eL.inv ≫ l := by
  rw [← cancel_mono (A'.obj.restrictOpenHom W), Category.assoc, hl, ← we, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id]
  simp

/-- The comparison of index categories is essentially surjective: an object of `Cris(X/S)` with a
morphism to `(U', T', δ')|_W` comes from an object of `Cris(U/T)` lying over `W`, by essential
surjectivity of `Crystalline.GlobalCrystallineSituation.pullbackCrisToComma`. -/
instance essSurj_rightToLeftIndex07MK : (rightToLeftIndex07MK S S' fS fX hf A').EssSurj where
  mem_essImage Y := by
    let Z : CostructuredArrow (crisToBig S S' fS fX hf) A'.obj :=
      CostructuredArrow.mk (Y.hom.unop ≫ A'.obj.restrictOpenHom Y.left.unop)
    let D := (pullbackCrisToComma S S' fS fX hf A').objPreimage Z
    let e := (pullbackCrisToComma S S' fS fX hf A').objObjPreimageIso Z
    let eL : (pullbackSmallChangeBase S S' fS fX hf A').obj D ≅ Y.right.unop :=
      (CostructuredArrow.proj _ _).mapIso e
    have we : (crisToBig S S' fS fX hf).map eL.hom ≫
        (Y.hom.unop ≫ A'.obj.restrictOpenHom Y.left.unop) =
          pullbackCommaProj S S' fS fX hf A' D.obj :=
      CostructuredArrow.w e.hom
    have hD : (forgetToOpens (pullbackSituation S S' fS fX hf A')).obj D ≤
        (pullbackOpensMap S S' fS fX hf A').obj Y.left.unop := by
      refine forgetToOpens_le_of_range_subset S S' fS fX hf A' D Y.left.unop ?_
      rw [← we]
      exact range_comp_comp_restrictOpenHom_subset S' A' Y.left.unop _ _
    let X : rightIndex07MK S S' fS fX hf A' := ⟨Y.left, op D, hD.hom.op⟩
    refine ⟨X, ⟨Comma.isoMk (Iso.refl _) eL.op.symm ?_⟩⟩
    apply Quiver.Hom.unop_inj
    refine Eq.trans ?_ (eq_crisToBig_map_inv_comp_of_restrictOpenHom S S' fS fX hf A' Y.left.unop
      Y.hom.unop eL we (pullbackCommaLift S S' fS fX hf A' X)
      (pullbackCommaLift_restrictOpenHom S S' fS fX hf A' X))
    exact congrArg Quiver.Hom.unop ((congrArg (· ≫ Y.hom)
      ((CrystallineThickening.restrictOpenFunctor A' ⋙ CrystallineThickening.ι S').op.map_id
        Y.left)).trans (Category.id_comp _))

/-- The comparison of index categories is an equivalence. -/
instance isEquivalence_rightToLeftIndex07MK :
    (rightToLeftIndex07MK S S' fS fX hf A').IsEquivalence := {}

/-- **The two index categories are equivalent over `T'_Zar`**: objects of `Cris(U/T)` lying over
an open `W` of `T'` are objects of `Cris(X/S)` with a morphism to `(U', T', δ')|_W` over
`S ⟶ S'`. -/
def rightToLeftIndexEquivalence07MK :
    rightIndex07MK S S' fS fX hf A' ≌ leftIndex07MK S S' fS fX hf A' :=
  (rightToLeftIndex07MK S S' fS fX hf A').asEquivalence

/-! ### The underived formula -/

/-- The square comparing the two index categories, over `T'_Zar`. -/
def indexTwoSquare07MK :
    TwoSquare (Comma.fst (pullbackOpensMap S S' fS fX hf A').op
        (forgetToOpens (pullbackSituation S S' fS fX hf A')).op)
      (rightToLeftIndex07MK S S' fS fX hf A') (𝟭 _)
      (Comma.fst (CrystallineThickening.restrictOpenFunctor A' ⋙ CrystallineThickening.ι S').op
        (crisToBigOp S S' fS fX hf)) :=
  TwoSquare.mk _ _ _ _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)).hom

/-- The `2`-cell of `indexTwoSquare07MK` is invertible. -/
instance isIso_indexTwoSquare07MK_natTrans : IsIso (indexTwoSquare07MK S S' fS fX hf A').natTrans :=
  inferInstanceAs (IsIso (NatIso.ofComponents _ _).hom)

/-- The presheaf underlying the left-hand side of the base case of (07MK), as a right Kan
extension along the projection of the left index category. -/
def leftSide07MKUnderivedPresheafIso :
    (crisDirectImage S S' fS fX hf ⋙ CrystallineThickening.abelianAmbientRestriction A') ⋙
        sheafToPresheaf (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (Comma.snd (CrystallineThickening.restrictOpenFunctor A' ⋙
            CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)) ⋙
        (Comma.fst (CrystallineThickening.restrictOpenFunctor A' ⋙
            CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)).ran :=
  Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (Functor.isoWhiskerRight (crisToBigRanIso S S' fS fX hf).symm
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (CrystallineThickening.restrictOpenFunctor A' ⋙ CrystallineThickening.ι S').op) ≪≫
      TwoSquare.ranCommaIso _ _)

/-- The presheaf underlying the right-hand side of the base case of (07MK), as a right Kan
extension along the projection of the right index category. -/
def rightSide07MKUnderivedPresheafIso :
    rightSide07MKUnderived S S' fS fX hf A' ⋙
        sheafToPresheaf (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (pullbackSmallChangeBase S S' fS fX hf A').op ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (Comma.snd (pullbackOpensMap S S' fS fX hf A').op
            (forgetToOpens (pullbackSituation S S' fS fX hf A')).op) ⋙
        (Comma.fst (pullbackOpensMap S S' fS fX hf A').op
            (forgetToOpens (pullbackSituation S S' fS fX hf A')).op).ran :=
  Functor.isoWhiskerRight (pullbackAbelianSheafIsoPullbackAbelianRestriction S S' fS fX hf A')
      (pullbackTauDirectImage S S' fS fX hf A' ⋙
        spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base ⋙
        sheafToPresheaf (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (pullbackSmallChangeBase S S' fS fX hf A').op)
      (TwoSquare.ranCommaIso (pullbackOpensMap S S' fS fX hf A').op
        (forgetToOpens (pullbackSituation S S' fS fX hf A')).op)

/-- The two right Kan extensions agree across the equivalence of index categories. -/
def indexRanIso07MK :
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (Comma.snd (CrystallineThickening.restrictOpenFunctor A' ⋙
            CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)) ⋙
        (Comma.fst (CrystallineThickening.restrictOpenFunctor A' ⋙
            CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)).ran ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (pullbackSmallChangeBase S S' fS fX hf A').op ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (Comma.snd (pullbackOpensMap S S' fS fX hf A').op
            (forgetToOpens (pullbackSituation S S' fS fX hf A')).op) ⋙
        (Comma.fst (pullbackOpensMap S S' fS fX hf A').op
            (forgetToOpens (pullbackSituation S S' fS fX hf A')).op).ran :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (Comma.snd (CrystallineThickening.restrictOpenFunctor A' ⋙
            CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)))
    (asIso (indexTwoSquare07MK S S' fS fX hf A').ranBaseChange)

/-- **The base case of (07MK)**: `(f_{cris, *}F)_{T'} ≅ (T ⟶ T')_*(τ_{U/T, *}F_U)`, naturally in
the abelian sheaf `F`. -/
def formulaBase07MK : FormulaBase07MK S S' fS fX hf A' :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1})
    (leftSide07MKUnderivedPresheafIso S S' fS fX hf A' ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
        (indexRanIso07MK S S' fS fX hf A') ≪≫
      (rightSide07MKUnderivedPresheafIso S S' fS fX hf A').symm)

/-! ### The derived formula -/

/-- The pullback `F ↦ F_U` is left exact. -/
instance preservesFiniteLimits_pullbackAbelianSheaf :
    PreservesFiniteLimits (pullbackAbelianSheaf S S' fS fX hf A') :=
  preservesFiniteLimits_crisInverseImage (pullbackSituation S S' fS fX hf A') S
    (pullback.fst fS A'.obj.toBase) (pullback.fst fX A'.obj.toX)
    (pullbackSituation_comm S S' fS fX hf A')

/-- The pullback `F ↦ F_U` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_pullbackAbelianSheaf :
    PreservesFiniteColimits (pullbackAbelianSheaf S S' fS fX hf A') := by
  unfold pullbackAbelianSheaf
  have := preservesColimitsOfSize_crisInverseImage.{0, 0} (pullbackSituation S S' fS fX hf A') S
    (pullback.fst fS A'.obj.toBase) (pullback.fst fX A'.obj.toX)
    (pullbackSituation_comm S S' fS fX hf A')
  exact ⟨fun _ _ _ => inferInstance⟩

/-- The pullback `F ↦ F_U` is additive. -/
instance additive_pullbackAbelianSheaf : (pullbackAbelianSheaf S S' fS fX hf A').Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `τ_{U/T, *}` with its target written as the small Zariski site of `T = S ×_{S'} T'`, the
source of `T ⟶ T'`. -/
def pullbackBaseTauDirectImage :
    Sheaf (smallTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology (pullbackBase S S' fS A').scheme.carrier)
        AddCommGrpCat.{u + 1} :=
  pullbackTauDirectImage S S' fS fX hf A'

/-- `τ_{U/T, *}` is additive. -/
instance additive_pullbackBaseTauDirectImage :
    (pullbackBaseTauDirectImage S S' fS fX hf A').Additive :=
  inferInstanceAs (tauDirectImage (pullbackSituation S S' fS fX hf A')).Additive

/-- `τ_{U/T, *}` carries injective abelian sheaves to injective abelian sheaves. -/
instance preservesInjectiveObjects_pullbackBaseTauDirectImage :
    (pullbackBaseTauDirectImage S S' fS fX hf A').PreservesInjectiveObjects :=
  inferInstanceAs (tauDirectImage (pullbackSituation S S' fS fX hf A')).PreservesInjectiveObjects

/-- The pullback `F ↦ F_U` carries injective abelian sheaves to injective abelian sheaves. -/
instance preservesInjectiveObjects_pullbackAbelianSheaf :
    (pullbackAbelianSheaf S S' fS fX hf A').PreservesInjectiveObjects where
  injective_obj {I} hI :=
    have := preservesInjectiveObjects_pullbackAbelianRestriction S S' fS fX hf A'
    Injective.of_iso
      ((pullbackAbelianSheafIsoPullbackAbelianRestriction S S' fS fX hf A').app I).symm
      ((pullbackAbelianRestriction S S' fS fX hf A').injective_obj_of_injective hI)

section Derived

attribute [local instance 2000] instHasSheafifyOpensSpaceAddCommGrpCat

variable [hX : HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [hX' : HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [hU : HasDerivedCategory.{w} (Sheaf (smallTopology (pullbackSituation S S' fS fX hf A'))
    AddCommGrpCat.{u + 1})]
  [hT : HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
    (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1})]
  [hT' : HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
    A'.obj.thickening.target.scheme.carrier) AddCommGrpCat.{u + 1})]

/-- The left-hand side of (07MK) is the derived functor of the underived left-hand side. -/
def leftSide07MKIso :
    leftSide07MK S S' fS fX hf A' ≅
      DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
        (crisDirectImage S S' fS fX hf ⋙
          CrystallineThickening.abelianAmbientRestriction A').rightDerivedFunctorPlus :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusCompIsoOfExact _ _ _ (Iso.refl _))

/-- `R((T ⟶ T')_* ∘ τ_{U/T, *}) ≅ Rτ_{U/T, *} ⋙ R(T ⟶ T')_*`, `τ_{U/T, *}` preserving injectives
([Stacks, Tag 015M]). -/
def derivedPullbackTauZariskiCompIso :
    (pullbackBaseTauDirectImage S S' fS fX hf A' ⋙
      spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus ≅
    (pullbackBaseTauDirectImage S S' fS fX hf A').rightDerivedFunctorPlus ⋙
      (spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIso _ _

/-- `R((T ⟶ T')_* ∘ τ_{U/T, *} ∘ (-)_U) ≅ R(-)_U ⋙ R((T ⟶ T')_* ∘ τ_{U/T, *})`, the pullback
`F ↦ F_U` preserving injectives ([Stacks, Tag 015M]). -/
def derivedPullbackAbelianSheafCompIso :
    (pullbackAbelianSheaf S S' fS fX hf A' ⋙ pullbackBaseTauDirectImage S S' fS fX hf A' ⋙
      spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus ≅
    (pullbackAbelianSheaf S S' fS fX hf A').rightDerivedFunctorPlus ⋙
    (pullbackBaseTauDirectImage S S' fS fX hf A' ⋙
      spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus :=
  Stacks.DerivedIndexing.rightDerivedPlusCompIso _ _

/-- `(F_U)[0] ≅ R(-)_U(F[0])`: the pullback `F ↦ F_U` is exact. -/
def pullbackAbelianSheafSingleIso :
    pullbackAbelianSheaf S S' fS fX hf A' ⋙ DerivedCategory.Plus.singleFunctor _ 0 ≅
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (pullbackAbelianSheaf S S' fS fX hf A').rightDerivedFunctorPlus :=
  haveI := Stacks.Cohomology.LerayDegreewise.isIso_rightDerivedPlusUnitSingle
    (pullbackAbelianSheaf S S' fS fX hf A') (Functor.rightAcyclic_of_exact _)
  asIso (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (pullbackAbelianSheaf S S' fS fX hf A'))

/-- The right-hand side of (07MK), with `τ_{U/T, *}` read with target `T_Zar`. -/
def rightSide07MKIsoComp : rightSide07MK S S' fS fX hf A' ≅ pullbackAbelianSheaf S S' fS fX hf A' ⋙
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (pullbackBaseTauDirectImage S S' fS fX hf A').rightDerivedFunctorPlus) ⋙
      (spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus :=
  Iso.refl _

/-- The underived right-hand side of (07MK), with `τ_{U/T, *}` read with target `T_Zar`. -/
def rightSide07MKUnderivedIso : rightSide07MKUnderived S S' fS fX hf A' ≅
    pullbackAbelianSheaf S S' fS fX hf A' ⋙ pullbackBaseTauDirectImage S S' fS fX hf A' ⋙
      spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base :=
  Iso.refl _

/-- The right-hand side of (07MK) is the derived functor of the underived right-hand side,
applied to `F[0]`. -/
def rightSide07MKIso :
    rightSide07MK S S' fS fX hf A' ≅
      DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
        (pullbackAbelianSheaf S S' fS fX hf A' ⋙ pullbackBaseTauDirectImage S S' fS fX hf A' ⋙
          spaceZariskiPushforward
            (pullback.snd fS A'.obj.toBase).hom.base).rightDerivedFunctorPlus :=
  rightSide07MKIsoComp S S' fS fX hf A' ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedPullbackTauZariskiCompIso S S' fS fX hf A').symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackAbelianSheafSingleIso S S' fS fX hf A') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedPullbackAbelianSheafCompIso S S' fS fX hf A').symm

/-- **The displayed equation (07MK) of [Stacks, Tag 07MJ]** at one object `(U', T', δ')`. -/
def formula07MK : Formula07MK.{w, w'} S S' fS fX hf A' :=
  leftSide07MKIso S S' fS fX hf A' ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorPlusNatIso
      (formulaBase07MK S S' fS fX hf A' ≪≫ rightSide07MKUnderivedIso S S' fS fX hf A')) ≪≫
    (rightSide07MKIso S S' fS fX hf A').symm

end Derived

/-- **Stacks Project, Tag 07MJ, the displayed equation (07MK).**  For every object
`(U', T', δ')` of `Cris(X'/S')`, with `U = X ×_{X'} U'` and `T = S ×_{S'} T'`,

`(Rf_{cris, *}F)_{T'} ≅ R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`

in `D⁺(Ab(T'_Zar))`, naturally in the abelian sheaf `F` on `Cris(X/S)`. -/
@[stacks 07MJ "the displayed equation (07MK): (Rf_{cris,*}F)_{T'} ≅ R(T ⟶ T')_*(Rτ_{U/T,*}F_U)
  in D⁺(Ab(T'_Zar)) for every object (U', T', δ') of Cris(X'/S'), naturally in F; stated for
  every abelian sheaf F on Cris(X/S), so in particular for the abelian sheaf underlying an
  O_{X/S}-module"]
theorem computes07MK
    [HasDerivedCategory.{u + 2} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 2} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})] :
    Computes07MK S S' fS fX hf := fun A' =>
  ⟨formula07MK.{u + 2, u + 2} S S' fS fX hf A'
    (hU := hasDerivedCategorySheaf (pullbackSituation S S' fS fX hf A'))
    (hT := hasDerivedCategorySpaceZariskiSheaf (pullbackBase S S' fS A').scheme.carrier)
    (hT' := hasDerivedCategorySpaceZariskiSheaf A'.obj.thickening.target.scheme.carrier)⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
