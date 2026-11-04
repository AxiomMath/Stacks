module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Over
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPull

/-!
# Push-pull along the localization at a semi-representable object over an object

Let `(C, J)` be a small site, `X` an object of `C` and `K = {U i / X}` a semi-representable
object over `X`. Restricting a sheaf on `C / X` to the componentwise localization site `C / K`
and pushing it forward again is the internal hom out of the sheaf associated to `K` on `C / X`:
`j_* j^{-1} F ≅ SheafHom(F(K)^#, F)`, naturally in `F`.

This is the Stacks 0D86 statement one level down, on the site `C / X` instead of `C`, and it is
deduced from it. Sheaves on `C / K` are families of sheaves on the sites `C / U i`, and the slice
site `C / U i` is the same as the slice of `C / X` at the object `U i / X`; under those two
identifications the restriction functor along `C / K ⥤ C / X` becomes the family of
localizations of `C / X` at the components of `K`. Its right adjoint is therefore the product of
the componentwise pushforwards, which Stacks 0D86 identifies with `SheafHom(F(K)^#, -)`.

## Main results

* `CategoryTheory.SemiRepresentable.componentwiseLocalizationPushforwardPullbackNatIsoSheafHom`:
  the identification of these two endofunctors of sheaves on `C / X`, naturally in the sheaf.

## Implementation notes

The source writes an equality of sheaves for each sheaf; the canonical, natural identification is
given here as an isomorphism of functors. The inverse image of a sheaf along the continuous
localization functor is `CategoryTheory.Functor.sheafPushforwardContinuous` and the direct image
is `CategoryTheory.Functor.sheafPushforwardCocontinuous`, whose names refer to the direction of
the functor between the sites.

## References

* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
-/

@[expose] public section

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.OverShriek

universe u

/-- The localization adjunction at a single object: restriction to the slice site is left adjoint
to pushforward from it. -/
noncomputable def localizationAdjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    localizationPullback U J ⊣ localizationPushforward U J := by
  simpa [localizationPullback, localizationPushforward] using
    (Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J

/-- The product of the componentwise localization pushforwards is right adjoint to the family of
componentwise restrictions. -/
noncomputable def componentLocalizationAdjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (K : FormalCoproduct.{u} C) :
    Functor.pi' (fun i : K.I => localizationPullback (K.obj i) J) ⊣
      Functor.pi (fun i : K.I => localizationPushforward (K.obj i) J) ⋙
        Pi.functor K.I := by
  apply Adjunction.mkOfHomEquiv
  refine
    { homEquiv := fun X F => by
        dsimp only [Functor.comp_obj, Pi.functor]
        exact (Equiv.piCongrRight (fun i =>
          (localizationAdjunction J (K.obj i)).homEquiv X (F i))).trans
          (productHomFamilyEquiv
            ((Functor.pi (fun i : K.I => localizationPushforward (K.obj i) J)).obj F) X).symm
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro X' X F f g
    funext i
    change ((localizationAdjunction J (K.obj i)).homEquiv X' (F i)).symm
        (f ≫ g ≫ Pi.π (fun j =>
          (localizationPushforward (K.obj j) J).obj (F j)) i) =
      (localizationPullback (K.obj i) J).map f ≫
        ((localizationAdjunction J (K.obj i)).homEquiv X (F i)).symm
          (g ≫ Pi.π (fun j =>
            (localizationPushforward (K.obj j) J).obj (F j)) i)
    simpa [Category.assoc] using
      (localizationAdjunction J (K.obj i)).homEquiv_naturality_left_symm f
        (g ≫ Pi.π (fun i =>
          (localizationPushforward (K.obj i) J).obj (F i)) i)
  · intro X F F' f g
    change (∀ j, (localizationPullback (K.obj j) J).obj X ⟶ F j) at f
    change (∀ j, F j ⟶ F' j) at g
    apply Pi.hom_ext
    intro i
    dsimp only [Functor.pi]
    change (productHomFamilyEquiv
        (fun j => (localizationPushforward (K.obj j) J).obj (F' j)) X).symm
        (fun j => (localizationAdjunction J (K.obj j)).homEquiv X (F' j)
          (f j ≫ g j)) ≫
        Pi.π (fun j => (localizationPushforward (K.obj j) J).obj (F' j)) i =
      (productHomFamilyEquiv
        (fun j => (localizationPushforward (K.obj j) J).obj (F j)) X).symm
        (fun j => (localizationAdjunction J (K.obj j)).homEquiv X (F j) (f j)) ≫
        Limits.Pi.map (fun j => (localizationPushforward (K.obj j) J).map (g j)) ≫
        Pi.π (fun j => (localizationPushforward (K.obj j) J).obj (F' j)) i
    simp only [productHomFamilyEquiv_symm_π, Pi.map_π]
    rw [← Category.assoc, productHomFamilyEquiv_symm_π]
    exact (localizationAdjunction J (K.obj i)).homEquiv_naturality_right (f i) (g i)

/-- The slice site of `C` at the domain of a component of `K` is the slice of `C / X` at that
component, read on sheaves. -/
noncomputable def iteratedSliceSheafEquivalence
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) (i : K.I) :
    Sheaf (J.over (K.obj i).left) (Type u) ≌
      Sheaf ((J.over X).over (K.obj i)) (Type u) :=
  ((K.obj i).iteratedSliceEquiv.sheafCongr
    ((J.over X).over (K.obj i)) (J.over (K.obj i).left) (Type u)).symm

/-- `iteratedSliceSheafEquivalence` on the whole family of components. -/
noncomputable def componentIteratedSliceEquivalence
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) :
    ((i : K.I) → Sheaf (J.over (K.obj i).left) (Type u)) ≌
      ((i : K.I) → Sheaf ((J.over X).over (K.obj i)) (Type u)) :=
  let E := fun i => iteratedSliceSheafEquivalence J X K i
  { functor := Functor.pi (fun i => (E i).functor)
    inverse := Functor.pi (fun i => (E i).inverse)
    unitIso := NatIso.pi (fun i => (E i).unitIso)
    counitIso := NatIso.pi (fun i => (E i).counitIso)
    functor_unitIso_comp := fun F => funext fun i => (E i).functor_unitIso_comp (F i) }

/-- Sheaves on `C / K` are families of sheaves on the slices of `C / X` at the components
of `K`. -/
noncomputable def componentwiseNestedSheavesEquivalence
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) :
    Sheaf (componentwiseTopology J
      (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C)) (Type u) ≌
      ((i : K.I) → Sheaf ((J.over X).over (K.obj i)) (Type u)) :=
  (formalCoproductSliceSheavesEquivalence J
      (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C) (Type u)).1.trans
    (componentIteratedSliceEquivalence J X K)

/-- Under the two identifications, restriction along `C / K ⥤ C / X` is the family of
localizations of `C / X` at the components of `K`. -/
noncomputable def componentwisePullbackToNested
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) :
    (componentwiseLocalizationFunctor K).sheafPushforwardContinuous
        (Type u)
        (componentwiseTopology J
          (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C))
        (J.over X) ⋙ (componentwiseNestedSheavesEquivalence J X K).functor ≅
      Functor.pi' (fun i => localizationPullback (K.obj i) (J.over X)) := by
  let K₀ : FormalCoproduct.{u} C := ⟨K.I, fun i => (K.obj i).left⟩
  let D := formalCoproductSliceSheavesEquivalence J K₀ (Type u)
  let E := componentIteratedSliceEquivalence J X K
  let F := componentwiseLocalizationFunctor K
  let J₀ := componentwiseTopology J K₀
  let G := F.sheafPushforwardContinuous (Type u) J₀ (J.over X)
  apply NatIso.pi'
  intro i
  let k := K.obj i
  let incl := CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K₀.obj j)) i
  let m := Over.map k.hom
  let e := k.iteratedSliceEquiv
  let Ei := iteratedSliceSheafEquivalence J X K i
  have : incl.IsContinuous (J.over (K₀.obj i)) J₀ := incl_isContinuous J K₀ i
  let hD₀ := (D.2 i).some
  let hD₀' := hD₀.trans
    ((incl.sheafPushforwardContinuousCompSheafToPresheafIso (Type u)
      (J.over (K₀.obj i)) J₀).symm)
  let hD := Functor.fullyFaithfulCancelRight
    (F := D.1.functor ⋙ Pi.eval _ i)
    (G := incl.sheafPushforwardContinuous (Type u) (J.over (K₀.obj i)) J₀)
    (sheafToPresheaf (J.over (K₀.obj i)) (Type u)) hD₀'
  let κ : incl ⋙ F ≅ m := by
    simpa [F, K₀, incl] using componentwiseLocalizationFunctorCompIso K i
  let eκ : e.functor ⋙ m ≅ Over.forget k := by
    have hInv : e.inverse = k.iteratedSliceBackward := rfl
    calc
      e.functor ⋙ Over.map k.hom = e.functor ⋙ (e.inverse ⋙ Over.forget k) := by
        rw [← Over.iteratedSliceBackward_forget k, ← hInv]
      _ ≅ (e.functor ⋙ e.inverse) ⋙ Over.forget k :=
        (Functor.associator _ _ _).symm
      _ ≅ (𝟭 _) ⋙ Over.forget k :=
        Functor.isoWhiskerRight e.unitIso.symm _
      _ ≅ Over.forget k := Functor.leftUnitor _
  have : e.functor.IsContinuous ((J.over X).over k) (J.over k.left) := inferInstance
  have : m.IsContinuous (J.over k.left) (J.over X) := inferInstance
  have : (incl ⋙ F).IsContinuous (J.over k.left) (J.over X) :=
    Functor.isContinuous_comp incl F (J.over k.left) J₀ (J.over X)
  have : (e.functor ⋙ m).IsContinuous ((J.over X).over k) (J.over X) :=
    Functor.isContinuous_comp e.functor m ((J.over X).over k)
      (J.over k.left) (J.over X)
  have hU : G ⋙ incl.sheafPushforwardContinuous (Type u) (J.over k.left) J₀ ≅
      m.sheafPushforwardContinuous (Type u) (J.over k.left) (J.over X) :=
    (Functor.sheafPushforwardContinuousComp incl F (Type u)
      (J.over k.left) J₀ (J.over X)).trans
        (Functor.sheafPushforwardContinuousIso κ (Type u)
          (J.over k.left) (J.over X))
  have hM : m.sheafPushforwardContinuous (Type u) (J.over k.left) (J.over X) ⋙
      e.functor.sheafPushforwardContinuous (Type u)
        ((J.over X).over k) (J.over k.left) ≅
      localizationPullback k (J.over X) := by
    simpa [localizationPullback] using
      (Functor.sheafPushforwardContinuousComp e.functor m (Type u)
          ((J.over X).over k) (J.over k.left) (J.over X)).trans
        (Functor.sheafPushforwardContinuousIso eκ (Type u)
          ((J.over X).over k) (J.over X))
  change (G ⋙ D.1.functor ⋙ E.functor ⋙ Pi.eval _ i) ≅
    localizationPullback k (J.over X)
  calc
    _ ≅ (G ⋙ D.1.functor) ⋙ (E.functor ⋙ Pi.eval _ i) :=
      Functor.associator _ _ _
    _ ≅ (G ⋙ D.1.functor) ⋙ (Pi.eval _ i ⋙ Ei.functor) :=
      Functor.isoWhiskerLeft _ (Iso.refl _)
    _ ≅ ((G ⋙ D.1.functor) ⋙ Pi.eval _ i) ⋙ Ei.functor :=
      (Functor.associator _ _ _).symm
    _ ≅ (G ⋙ (D.1.functor ⋙ Pi.eval _ i)) ⋙ Ei.functor :=
      Functor.isoWhiskerRight (Functor.associator _ _ _) Ei.functor
    _ ≅ (G ⋙ incl.sheafPushforwardContinuous (Type u) (J.over k.left) J₀) ⋙
        Ei.functor :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft G hD) Ei.functor
    _ ≅ m.sheafPushforwardContinuous (Type u) (J.over k.left) (J.over X) ⋙
        Ei.functor := Functor.isoWhiskerRight hU Ei.functor
    _ ≅ localizationPullback k (J.over X) := by
      change m.sheafPushforwardContinuous (Type u) (J.over k.left) (J.over X) ⋙
          e.functor.sheafPushforwardContinuous (Type u)
            ((J.over X).over k) (J.over k.left) ≅ _
      exact hM

/-- Dually, the product of the componentwise pushforwards is pushforward along
`C / K ⥤ C / X`. -/
noncomputable def componentwisePushforwardFromNested
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) :
    Functor.pi (fun i : K.I => localizationPushforward (K.obj i) (J.over X)) ⋙
        Pi.functor K.I ≅
      (componentwiseNestedSheavesEquivalence J X K).inverse ⋙
        (componentwiseLocalizationFunctor K).sheafPushforwardCocontinuous
          (Type u)
          (componentwiseTopology J
            (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C))
          (J.over X) := by
  let K₀ : FormalCoproduct.{u} C := ⟨K.I, fun i => (K.obj i).left⟩
  let E := componentwiseNestedSheavesEquivalence J X K
  let F := componentwiseLocalizationFunctor K
  let J₀ := componentwiseTopology J K₀
  exact (componentLocalizationAdjunction (J.over X) K).rightAdjointUniq
    (((F.sheafAdjunctionCocontinuous (Type u) J₀ (J.over X)).comp E.toAdjunction).ofNatIsoLeft
      (componentwisePullbackToNested J X K))

/-- **Stacks 0D89.** The localization push-pull on `C / X` at a semi-representable object `K`
over `X` is naturally the sheaf internal hom out of the sheafification of the semi-representable
presheaf associated to `K`. -/
@[stacks 0D89 "push_pull"]
noncomputable def componentwiseLocalizationPushforwardPullbackNatIsoSheafHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{u} (Over X)) :
    ((componentwiseLocalizationFunctor K).sheafPushforwardContinuous
      (Type u)
      (componentwiseTopology J
        (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C))
      (J.over X)) ⋙
      ((componentwiseLocalizationFunctor K).sheafPushforwardCocontinuous
        (Type u)
        (componentwiseTopology J
          (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{u} C))
        (J.over X)) ≅
      CategoryTheory.SheafHomAdj.sheafHomFunctor
        ((presheafToSheaf (J.over X) (Type u)).obj
        ((FormalCoproduct.yoneda (C := Over X)).obj K)) := by
  let K₀ : FormalCoproduct.{u} C := ⟨K.I, fun i => (K.obj i).left⟩
  let F := componentwiseLocalizationFunctor K
  let J₀ := componentwiseTopology J K₀
  let E := componentwiseNestedSheavesEquivalence J X K
  let P := F.sheafPushforwardContinuous (Type u) J₀ (J.over X)
  let Q := F.sheafPushforwardCocontinuous (Type u) J₀ (J.over X)
  let L := Functor.pi' (fun i : K.I => localizationPullback (K.obj i) (J.over X))
  let R := Functor.pi (fun i : K.I => localizationPushforward (K.obj i) (J.over X)) ⋙
    Pi.functor K.I
  let hLR : P ⋙ Q ≅ L ⋙ R := by
    calc
      _ ≅ (P ⋙ (𝟭 _)) ⋙ Q :=
        (Functor.isoWhiskerRight (Functor.rightUnitor P) Q).symm
      _ ≅ P ⋙ ((𝟭 _) ⋙ Q) :=
        Functor.associator _ _ _
      _ ≅ P ⋙ ((E.functor ⋙ E.inverse) ⋙ Q) :=
        Functor.isoWhiskerLeft P (Functor.isoWhiskerRight E.unitIso Q)
      _ ≅ (P ⋙ (E.functor ⋙ E.inverse)) ⋙ Q :=
        (Functor.associator _ _ _).symm
      _ ≅ ((P ⋙ E.functor) ⋙ E.inverse) ⋙ Q :=
        Functor.isoWhiskerRight (Functor.associator P E.functor E.inverse) Q
      _ ≅ (L ⋙ E.inverse) ⋙ Q :=
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight (componentwisePullbackToNested J X K) E.inverse) Q
      _ ≅ L ⋙ (E.inverse ⋙ Q) :=
        Functor.associator _ _ _
      _ ≅ L ⋙ R := Functor.isoWhiskerLeft L (componentwisePushforwardFromNested J X K).symm
  exact hLR.trans ((Functor.associator _ _ _).symm.trans
    (localizationPushforwardPullbackNatIsoSheafHom (J.over X) K))

end CategoryTheory.SemiRepresentable

end
