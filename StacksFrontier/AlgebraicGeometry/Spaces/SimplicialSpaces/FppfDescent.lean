module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebra
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition

/-!
# Descent of spaces-étale sheaves along flat, locally finitely presented, surjective morphisms

This file records the statement of effective descent of sheaves on spaces-étale sites along a
morphism of algebraic spaces which is flat, locally of finite presentation and surjective: the
flat case of Stacks 0GFW, in the form
`AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_isFlat` states it, under the
name `AlgebraicGeometry.Space.EffectiveFppfDescent`; it is proved from that theorem as
`AlgebraicGeometry.Space.effectiveFppfDescent` in
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringInverseImage`. The
consequences drawn from it here are those a descent argument uses: inverse images along such
morphisms are faithful, morphisms satisfying the cocycle condition over the fibre product descend,
and descent data are effective.

The file also records the stability of the class of flat, locally finitely presented, surjective
morphisms under base change and composition.

## Main definitions

* `AlgebraicGeometry.Space.EffectiveFppfDescent`: effective descent of spaces-étale sheaves along
  flat, locally finitely presented, surjective morphisms.

## Main results

* `AlgebraicGeometry.Space.fppfSurjective_of_isPullback` and `.fppfSurjective_comp`: flat,
  locally finitely presented, surjective morphisms are stable under base change and composition.
* `AlgebraicGeometry.Space.EffectiveFppfDescent.map_injective`, `.exists_map_eq` and
  `.exists_iso`: faithfulness of inverse images, descent of morphisms, and effectivity of descent
  data.

## References

* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Effective descent of spaces-étale sheaves along fppf coverings**: along every morphism of
algebraic spaces over `S` which is surjective, flat and locally of finite presentation, sheaves on
the spaces-étale site of the target are equivalent, through the canonical descent datum, to
descent data for the one-member family. This is the flat case of Stacks 0GFW. -/
def EffectiveFppfDescent : Prop :=
  ∀ ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y), IsSurjective B S hS f.hom →
    IsFlat B S hS f.hom → IsLocallyOfFinitePresentation B S hS f.hom →
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence

variable {B S hS}

/-! ### Flat, locally finitely presented, surjective morphisms -/

/-- A base change of a flat, locally finitely presented, surjective morphism is again one. -/
theorem fppfSurjective_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f) (hg : fppfSurjective B S hS g) : fppfSurjective B S hS q :=
  ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hg.1,
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hg.2.1,
    isSurjective_of_isPullback B S hS sq hg.2.2⟩

/-- A composite of flat, locally finitely presented, surjective morphisms is again one. -/
theorem fppfSurjective_comp {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : fppfSurjective B S hS f) (hg : fppfSurjective B S hS g) :
    fppfSurjective B S hS (f ≫ g) :=
  ⟨isFlat_comp B S hS X.property Y.property Z.property f.hom g.hom hf.1 hg.1,
    isLocallyOfFinitePresentation_comp B S hS X.property Y.property Z.property f.hom g.hom
      hf.2.1 hg.2.1,
    isSurjective_comp B S hS hf.2.2 hg.2.2⟩

/-! ### Pulling back morphisms -/

section PullHom

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₂, u₂}}

/-- Pulling back an identity gives an identity. -/
theorem pullHom_id_eq_id ⦃X : C⦄ (M : F.obj (.mk (op X))) ⦃Y : C⦄ (f : Y ⟶ X) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom (F := F) (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf gf hgf hgf = 𝟙 _ := by
  simp [pullHom]

/-- Pulling back along a morphism whose inverse image is faithful is injective. -/
theorem pullHom_injective ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂)
    (hinj : ∀ {P Q : F.obj (.mk (op Y))} (a b : P ⟶ Q),
      (F.map g.op.toLoc).toFunctor.map a = (F.map g.op.toLoc).toFunctor.map b → a = b)
    (h : pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂) : φ = φ' := by
  apply hinj
  rw [map_eq_pullHom φ g gf₁ gf₂ hgf₁ hgf₂, map_eq_pullHom φ' g gf₁ gf₂ hgf₁ hgf₂, h]

/-- Cancelling a compositor against its inverse between two inverse images of morphisms. -/
theorem map_mapComp'_inv_hom_map {X₀ Y₀ Z₀ : C} (f : Y₀ ⟶ X₀) (g : Z₀ ⟶ Y₀) (fg : Z₀ ⟶ X₀)
    (h : f.op.toLoc ≫ g.op.toLoc = fg.op.toLoc)
    {P : F.obj (.mk (op Y₀))} {M : F.obj (.mk (op X₀))}
    (a : P ⟶ (F.map f.op.toLoc).toFunctor.obj M) (b : (F.map f.op.toLoc).toFunctor.obj M ⟶ P) :
    (F.map g.op.toLoc).toFunctor.map a ≫
        (F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc h).inv.toNatTrans.app M ≫
        (F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc h).hom.toNatTrans.app M ≫
        (F.map g.op.toLoc).toFunctor.map b =
      (F.map g.op.toLoc).toFunctor.map (a ≫ b) := by
  simp

/-- Pulling back along equal morphisms. -/
theorem pullHom_congr_left ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ {g g' : Y' ⟶ Y} (hg : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₁' : g' ≫ f₁ = gf₁) (h₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ = pullHom φ g' gf₁ gf₂ h₁' h₂' := by
  subst hg
  rfl

/-- Changing the second composite of a pulled-back morphism along an equality. -/
theorem pullHom_comp_eqToHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) {gf₂ gf₂' : Y' ⟶ X₂} (e : gf₂ = gf₂')
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₂' : g ≫ f₂ = gf₂') :
    pullHom φ g gf₁ gf₂ h₁ h₂ ≫
        eqToHom (congrArg (fun t : Y' ⟶ X₂ => (F.map t.op.toLoc).toFunctor.obj M₂) e) =
      pullHom φ g gf₁ gf₂' h₁ h₂' := by
  subst e
  simp

/-- Pulling back an identity along two equal composites gives the identification. -/
theorem pullHom_id_eq_eqToHom ⦃X : C⦄ (M : F.obj (.mk (op X))) ⦃Y : C⦄ (f : Y ⟶ X) ⦃Y' : C⦄
    (g : Y' ⟶ Y) {gf₁ gf₂ : Y' ⟶ X} (e : gf₁ = gf₂) (h₁ : g ≫ f = gf₁) (h₂ : g ≫ f = gf₂) :
    pullHom (F := F) (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf₁ gf₂ h₁ h₂ =
      eqToHom (congrArg (fun t : Y' ⟶ X => (F.map t.op.toLoc).toFunctor.obj M) e) := by
  subst e
  simp [pullHom]

/-- The opposite morphisms of a composite, as morphisms in the locally discrete category. -/
private theorem op_toLoc_comp_eq {a b c : C} {x : a ⟶ b} {y : b ⟶ c} {xy : a ⟶ c}
    (h : x ≫ y = xy) : y.op.toLoc ≫ x.op.toLoc = xy.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]

/-- **Transport of a morphism along a factorization, pulled back.** Let `α` be a morphism between
two inverse images of `N` over `Y`, along `y₁ = e ≫ p₁` and `y₂ = e ≫ p₂`. Its transport to a
morphism between the inverse images along `e` of `p₁^* N` and `p₂^* N`, pulled back along `k`,
is the pullback of `α` along `k`, transported in the same way. -/
theorem pullHom_transport {X₀ P Y Y' : C} {N : F.obj (.mk (op X₀))} (p₁ p₂ : P ⟶ X₀)
    (e : Y ⟶ P) (y₁ y₂ : Y ⟶ X₀) (hy₁ : e ≫ p₁ = y₁) (hy₂ : e ≫ p₂ = y₂)
    (α : (F.map y₁.op.toLoc).toFunctor.obj N ⟶ (F.map y₂.op.toLoc).toFunctor.obj N)
    (k : Y' ⟶ Y) (r : Y' ⟶ P) (hr : k ≫ e = r) (z₁ z₂ : Y' ⟶ X₀) (hz₁ : r ≫ p₁ = z₁)
    (hz₂ : r ≫ p₂ = z₂) :
    pullHom (F := F) ((F.mapComp' p₁.op.toLoc e.op.toLoc y₁.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hy₁])).inv.toNatTrans.app N ≫ α ≫
        (F.mapComp' p₂.op.toLoc e.op.toLoc y₂.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hy₂])).hom.toNatTrans.app N) k r r hr hr =
      (F.mapComp' p₁.op.toLoc r.op.toLoc z₁.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hz₁])).inv.toNatTrans.app N ≫
        pullHom α k z₁ z₂ (by rw [← hz₁, ← hr, Category.assoc, hy₁])
          (by rw [← hz₂, ← hr, Category.assoc, hy₂]) ≫
        (F.mapComp' p₂.op.toLoc r.op.toLoc z₂.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hz₂])).hom.toNatTrans.app N := by
  subst hy₁ hy₂ hr hz₁ hz₂
  simp only [pullHom, Functor.map_comp, Category.assoc]
  have hc : ∀ {a b c : C} (x : a ⟶ b) (y : b ⟶ c),
      y.op.toLoc ≫ x.op.toLoc = (x ≫ y).op.toLoc := fun _ _ => op_toLoc_comp_eq rfl
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc p₁.op.toLoc e.op.toLoc k.op.toLoc
      (e ≫ p₁).op.toLoc (k ≫ e).op.toLoc ((k ≫ e) ≫ p₁).op.toLoc (hc _ _) (hc _ _)
      (hc _ _),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app p₂.op.toLoc e.op.toLoc k.op.toLoc
      (e ≫ p₂).op.toLoc (k ≫ e).op.toLoc ((k ≫ e) ≫ p₂).op.toLoc (hc _ _) (hc _ _)
      (by rw [hc, Category.assoc])]

/-- A morphism between inverse images along `f` whose two pullbacks to the fibre product of `f`
with itself agree is compatible with the canonical comparisons there. -/
theorem descentSquareApp_comm_of_pullHom_eq {S' X : C} {f : X ⟶ S'} (sq : ChosenPullback f f)
    {M N : F.obj (.mk (op S'))}
    (h : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (H : pullHom h sq.p₁ sq.p sq.p sq.hp₁ sq.hp₁ = pullHom h sq.p₂ sq.p sq.p sq.hp₂ sq.hp₂) :
    (F.map sq.p₁.op.toLoc).toFunctor.map h ≫ descentSquareApp sq N =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map h := by
  have H' := congrArg (fun t => (descentPullbackIso₁ sq).inv.toNatTrans.app M ≫ t ≫
    (descentPullbackIso₂ sq).hom.toNatTrans.app N) H
  dsimp only [pullHom, descentPullbackIso₁, descentPullbackIso₂] at H'
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app] at H'
  simp only [descentSquareApp, descentPullbackIso₁, descentPullbackIso₂, Category.assoc]
  exact H'.trans (congrArg (_ ≫ _ ≫ ·) (Category.comp_id _))

/-- A morphism over `P` whose inverse image along `e` is the transport of `α` pulls back along `e`
to `α`. -/
theorem pullHom_eq_of_map_eq {X₀ P Y : C} {N : F.obj (.mk (op X₀))} (p₁ p₂ : P ⟶ X₀)
    (e : Y ⟶ P) (y₁ y₂ : Y ⟶ X₀) (hy₁ : e ≫ p₁ = y₁) (hy₂ : e ≫ p₂ = y₂)
    (φ : (F.map p₁.op.toLoc).toFunctor.obj N ⟶ (F.map p₂.op.toLoc).toFunctor.obj N)
    (α : (F.map y₁.op.toLoc).toFunctor.obj N ⟶ (F.map y₂.op.toLoc).toFunctor.obj N)
    (h : (F.map e.op.toLoc).toFunctor.map φ =
      (F.mapComp' p₁.op.toLoc e.op.toLoc y₁.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hy₁])).inv.toNatTrans.app N ≫ α ≫
        (F.mapComp' p₂.op.toLoc e.op.toLoc y₂.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hy₂])).hom.toNatTrans.app N) :
    pullHom φ e y₁ y₂ hy₁ hy₂ = α := by
  rw [map_eq_pullHom φ e y₁ y₂ hy₁ hy₂] at h
  have := congrArg (fun t => (F.mapComp' p₁.op.toLoc e.op.toLoc y₁.op.toLoc
      (op_toLoc_comp_eq hy₁)).hom.toNatTrans.app N ≫ t ≫
    (F.mapComp' p₂.op.toLoc e.op.toLoc y₂.op.toLoc
      (op_toLoc_comp_eq hy₂)).inv.toNatTrans.app N) h
  simpa using this

end PullHom

/-! ### Consequences of effective descent -/

namespace EffectiveFppfDescent

variable (hdesc : EffectiveFppfDescent B S hS)
include hdesc

/-- Under effective fppf descent, the descent functor along a flat, locally finitely presented,
surjective morphism is an equivalence. -/
theorem isEquivalence {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : fppfSurjective B S hS f) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence :=
  hdesc f hf.2.2 hf.1 hf.2.1

/-- **Inverse images along fppf coverings are faithful.** -/
theorem map_injective {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : fppfSurjective B S hS f) {M N : spacesEtaleSheafCat B S hS Y} {a b : M ⟶ N}
    (h : (spacesEtaleInverseImage B S hS f).map a = (spacesEtaleInverseImage B S hS f).map b) :
    a = b := by
  have := hdesc.isEquivalence hf
  apply ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).map_injective
  ext ⟨⟩
  exact h

/-- **Morphisms descend along fppf coverings**: a morphism between the inverse images of two
sheaves which is compatible with the canonical comparisons over the fibre product is the inverse
image of a morphism. -/
theorem exists_map_eq {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : fppfSurjective B S hS f) (sq : ChosenPullback f f)
    {M N : spacesEtaleSheafCat B S hS Y}
    (h : (spacesEtaleInverseImage B S hS f).obj M ⟶ (spacesEtaleInverseImage B S hS f).obj N)
    (hcomm : ((spacesEtalePseudofunctor B S hS).map sq.p₁.op.toLoc).toFunctor.map h ≫
        descentSquareApp (F := spacesEtalePseudofunctor B S hS) sq N =
      descentSquareApp (F := spacesEtalePseudofunctor B S hS) sq M ≫
        ((spacesEtalePseudofunctor B S hS).map sq.p₂.op.toLoc).toFunctor.map h) :
    ∃ u : M ⟶ N, (spacesEtaleInverseImage B S hS f).map u = h := by
  have := hdesc.isEquivalence hf
  let φ : DescentData.ofObj (F := spacesEtalePseudofunctor B S hS) (f := fun _ : Unit => f) M ⟶
      DescentData.ofObj N :=
    { hom := fun _ => h
      comm := fun _ q _ _ f₁ f₂ hf₁ hf₂ =>
        descentComparison_comm_of_comm (F := spacesEtalePseudofunctor B S hS) (M := M) (N := N)
          sq h hcomm q f₁ f₂ hf₁ hf₂ }
  obtain ⟨u, hu⟩ := ((spacesEtalePseudofunctor B S hS).toDescentData
    (fun _ : Unit => f)).map_surjective φ
  exact ⟨u, congrArg (fun t => DescentData.Hom.hom t ()) hu⟩

/-- **Descent data along fppf coverings are effective.** -/
theorem exists_iso {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : fppfSurjective B S hS f)
    (D : (spacesEtalePseudofunctor B S hS).DescentData (fun _ : Unit => f)) :
    ∃ M : spacesEtaleSheafCat B S hS Y,
      Nonempty (((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).obj M ≅
        D) := by
  have := hdesc.isEquivalence hf
  exact ⟨_, ⟨((spacesEtalePseudofunctor B S hS).toDescentData
    (fun _ : Unit => f)).objObjPreimageIso D⟩⟩

end EffectiveFppfDescent

end AlgebraicGeometry.Space
