module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# The étale base change map for sheaves of sets and for abelian sheaves

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
there are two base change maps `g^{-1} f_* ⟶ f'_* (g')^{-1}`: one on sheaves of sets,
`Stacks.EtaleCohomology.smallEtaleSetBaseChange`, and one on abelian sheaves,
`Stacks.EtaleCohomology.etaleAbelianBaseChange`. This file relates them through the forgetful
functor `U` from abelian sheaves to sheaves of sets.

Direct image commutes with `U` on the nose, and inverse image commutes with `U` up to the
canonical isomorphism `Stacks.EtaleCohomology.coefficientPullbackTwoSquare`. The cube identity
of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` then says that `U` carries the abelian base
change map at `A` to the set base change map at `U A`, up to these isomorphisms
(`Stacks.EtaleCohomology.forget_etaleAbelianBaseChange`). So one is invertible exactly when the
other is.

## Main results

* `Stacks.EtaleCohomology.forget_etaleAbelianBaseChange` — the cube identity.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_forget_iff` — the abelian base change map
  is invertible at `A` exactly when the set base change map is invertible at `U A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Abstract

variable {C D E F C' D' E' F' : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [Category* C'] [Category* D'] [Category* E'] [Category* F']
  {L₁ : C ⥤ D} {L₂ : E ⥤ F} {L₁' : C' ⥤ D'} {L₂' : E' ⥤ F'}
  {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
  {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}

/-- The component form of an identity between a horizontal pasting and a whiskered horizontal
pasting of 2-squares, as produced by `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`. -/
lemma hComp_app_of_eq (w : TwoSquare G L₁ L₂ H) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
    (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (w' : TwoSquare G' L₁' L₂' H')
    (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
    (heq : w ≫ₕ τ₂ = ((τ₁ ≫ₕ w').whiskerTop σG).whiskerBottom σH) (c : C) :
    τ₂.app (G.obj c) ≫ ΦF.map (w.app c) =
      L₂'.map (σG.app c) ≫ w'.app (ΦC.obj c) ≫ H'.map (τ₁.app c) ≫
        σH.app (L₁.obj c) := by
  have := congrArg (fun z ↦ z.app c) heq
  simpa [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using this

end Abstract

section Forget

/-- The forgetful functor from abelian sheaves to sheaves of sets on the small étale site. -/
abbrev etaleForget (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ Sheaf S.smallEtaleTopology (Type (u + 1)) :=
  sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})

/-- The comparison `k^{-1} (U M) ⟶ U (k^{-1} M)` of the two composites of inverse image with the
forgetful functor. It is invertible
(`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`). -/
abbrev etaleForgetPullback {S T : Scheme.{u}} (k : T ⟶ S) :
    TwoSquare (etaleForget S) (etaleAbelianInverseImage.{u, 0} k)
      (smallEtaleInverseImage.{u, 0} k) (etaleForget T) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange k) S.smallEtaleTopology T.smallEtaleTopology
    (forget AddCommGrpCat.{u + 1})

/-- The comparison of inverse image with the forgetful functor is a natural isomorphism. -/
private instance isIso_etaleForgetPullback_natTrans {S T : Scheme.{u}} (k : T ⟶ S) :
    IsIso (etaleForgetPullback k) :=
  isIso_coefficientPullbackTwoSquare _ _ _ _

/-- The forgetful functor carries the composition comparison of direct images at abelian
coefficients to the one at set coefficients. -/
lemma etaleForget_map_pushforwardComp'_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleForget Z).map ((smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app M) =
      (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app ((etaleForget X).obj M) :=
  rfl

/-- The forgetful functor carries the inverse of the composition comparison of direct images at
abelian coefficients to the one at set coefficients. -/
lemma etaleForget_map_pushforwardComp'_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleForget Z).map ((smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).inv.app M) =
      (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).inv.app ((etaleForget X).obj M) :=
  rfl

/-- The composition comparison of direct images with the composite named, at the composite
itself, is the unnamed one. -/
lemma smallEtalePushforwardComp'_rfl_eq_smallEtalePushforwardCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePushforwardComp' f g (f ≫ g) rfl (Type (u + 1)) =
      smallEtalePushforwardCompIso.{u, 0} f g := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))))
  simp [smallEtalePushforwardComp', smallEtalePushforwardCompIso, smallEtaleBaseChangeComp']
  rfl

/-- Moving the name of the composite in the composition comparison of direct images. -/
lemma smallEtalePushforwardComp'_inv_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).inv =
      eqToHom (congrArg (fun k : X ⟶ Z ↦ smallEtalePushforward k (Type (u + 1))) hfg) ≫
        (smallEtalePushforwardComp' f g (f ≫ g) rfl (Type (u + 1))).inv := by
  subst hfg
  simp

/-- The comparison of composite direct images in the definition of
`Stacks.EtaleCohomology.smallEtaleSetBaseChange`, written with the composite named. -/
lemma smallEtaleSetBaseChange_twoSquare_eq {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g) :
    (smallEtalePushforwardCompIso.{u, 0} g' f).hom ≫
        (eqToIso (congrArg (fun k : X' ⟶ Y ↦
          (smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) 0)) (smallEtaleTopology Y) (smallEtaleTopology X')) h)).hom ≫
        (smallEtalePushforwardCompIso.{u, 0} f' g).inv =
      (smallEtalePushforwardComp' g' f (g' ≫ f) rfl (Type (u + 1))).hom ≫
        (smallEtalePushforwardComp' f' g (g' ≫ f) h (Type (u + 1))).inv := by
  rw [smallEtalePushforwardComp'_inv_eq,
    smallEtalePushforwardComp'_rfl_eq_smallEtalePushforwardCompIso,
    smallEtalePushforwardComp'_rfl_eq_smallEtalePushforwardCompIso]
  rfl

/-- **The set base change map is the mate of the comparison of composite direct images**, with
the composite named. -/
lemma smallEtaleSetBaseChange_eq_mateEquiv_symm {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g) :
    smallEtaleSetBaseChange.{u, 0} g' f' f g h =
      ((mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} g')
          (smallEtaleInverseImageAdjunction.{u, 0} g)).symm
        (TwoSquare.mk _ _ _ _
          ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl (Type (u + 1))).hom ≫
            (smallEtalePushforwardComp' f' g (g' ≫ f) h (Type (u + 1))).inv))) := by
  rw [← smallEtaleSetBaseChange_twoSquare_eq]
  rfl

section Cube

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The comparison of composite direct images at abelian coefficients, as a 2-square. -/
abbrev abelianDirectImageSquare :
    TwoSquare (etaleAbelianDirectImage.{u, 0} g') (etaleAbelianDirectImage.{u, 0} f')
      (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDirectImage.{u, 0} g) :=
  TwoSquare.mk _ _ _ _
    ((etaleAbelianDirectImageCompIso'.{u, 0} g' f (g' ≫ f) rfl).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, 0} f' g (g' ≫ f) h).inv)

/-- The comparison of composite direct images at set coefficients, as a 2-square. -/
abbrev setDirectImageSquare :
    TwoSquare (smallEtalePushforward g' (Type (u + 1))) (smallEtalePushforward f' (Type (u + 1)))
      (smallEtalePushforward f (Type (u + 1))) (smallEtalePushforward g (Type (u + 1))) :=
  TwoSquare.mk _ _ _ _
    ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl (Type (u + 1))).hom ≫
      (smallEtalePushforwardComp' f' g (g' ≫ f) h (Type (u + 1))).inv)

/-- The hypothesis of the cube identity: the two comparisons of composite direct images agree
after forgetting the group structure, every side comparison through a direct image being the
identity. -/
theorem forget_directImageSquare :
    ((mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
          (smallEtaleInverseImageAdjunction.{u, 0} g') (etaleForgetPullback g') ≫ᵥ
        setDirectImageSquare f g g' f' h).whiskerRight
          (𝟙 (etaleAbelianDirectImage.{u, 0} f ⋙ etaleForget Y))).whiskerLeft
          (𝟙 (etaleForget X' ⋙ smallEtalePushforward f' (Type (u + 1)))) =
      abelianDirectImageSquare f g g' f' h ≫ᵥ
        mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
          (smallEtaleInverseImageAdjunction.{u, 0} g) (etaleForgetPullback g) := by
  have h₁ : mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
      (smallEtaleInverseImageAdjunction.{u, 0} g') (etaleForgetPullback g') =
      coefficientPushforwardTwoSquare (smallEtaleBaseChange g')
        X.smallEtaleTopology X'.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) :=
    mateEquiv_coefficientPullbackTwoSquare _ _ _ _
  have h₂ : mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
      (smallEtaleInverseImageAdjunction.{u, 0} g) (etaleForgetPullback g) =
      coefficientPushforwardTwoSquare (smallEtaleBaseChange g)
        Y.smallEtaleTopology Y'.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) :=
    mateEquiv_coefficientPullbackTwoSquare _ _ _ _
  rw [h₁, h₂]
  refine NatTrans.ext (funext fun M ↦ ?_)
  rfl

/-- **The forgetful functor carries the abelian base change map to the set base change map**,
up to the comparisons of inverse image with the forgetful functor: for an abelian sheaf `M` on
`X_étale`, the square
```
g^{-1} U f_* M ----> U g^{-1} f_* M
   |                     |
   v                     v
f'_* (g')^{-1} U M --> f'_* U (g')^{-1} M
```
commutes, the vertical maps being the base change maps at set and at abelian coefficients. -/
theorem forget_etaleAbelianBaseChange_app (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleForgetPullback g).app ((etaleAbelianDirectImage.{u, 0} f).obj M) ≫
        (etaleForget Y').map ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app M) =
      (smallEtaleSetBaseChange.{u, 0} g' f' f g h).app ((etaleForget X).obj M) ≫
        (smallEtalePushforward f' (Type (u + 1))).map
          ((etaleForgetPullback g').app M) := by
  have key := hComp_app_of_eq _ _ _ _ _ _
    (Stacks.CategoryTheory.mateEquiv_symm_hComp_eq
      (G := etaleAbelianDirectImage.{u, 0} f) (H := etaleAbelianDirectImage.{u, 0} f')
      (G' := smallEtalePushforward f (Type (u + 1)))
      (H' := smallEtalePushforward f' (Type (u + 1)))
      (ΦC := etaleForget X) (ΦD := etaleForget X') (ΦE := etaleForget Y) (ΦF := etaleForget Y')
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
      (smallEtaleInverseImageAdjunction.{u, 0} g') (smallEtaleInverseImageAdjunction.{u, 0} g)
      (etaleForgetPullback g') (etaleForgetPullback g)
      (𝟙 (etaleAbelianDirectImage.{u, 0} f ⋙ etaleForget Y))
      (𝟙 (etaleForget X' ⋙ smallEtalePushforward f' (Type (u + 1))))
      (abelianDirectImageSquare f g g' f' h) (setDirectImageSquare f g g' f' h)
      (forget_directImageSquare f g g' f' h)) M
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0} f g g' f' h (g' ≫ f)
    rfl h, smallEtaleSetBaseChange_eq_mateEquiv_symm]
  refine key.trans ?_
  exact congrArg (fun z ↦ z ≫ _) ((smallEtaleInverseImage.{u, 0} g).map_id _) |>.trans
    ((Category.id_comp _).trans (congrArg (fun z ↦ _ ≫ z) (Category.comp_id _)))

/-- **The abelian base change map is invertible at `M` exactly when the set base change map is
invertible at the underlying sheaf of sets of `M`.** -/
theorem isIso_etaleAbelianBaseChange_app_iff
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app M) ↔
      IsIso ((smallEtaleSetBaseChange.{u, 0} g' f' f g h).app ((etaleForget X).obj M)) := by
  have key := forget_etaleAbelianBaseChange_app f g g' f' h M
  have : IsIso ((smallEtalePushforward f' (Type (u + 1))).map
      ((etaleForgetPullback g').app M)) := inferInstance
  rw [← isIso_iff_of_reflects_iso _ (etaleForget Y'),
    ← isIso_comp_left_iff
      ((etaleForgetPullback g).app ((etaleAbelianDirectImage.{u, 0} f).obj M)), key]
  exact @isIso_comp_right_iff _ _ _ _ _ _ _ this

/-- **Transport of base change from sheaves of sets to abelian sheaves.** If the base change map
of a commutative square is invertible on sheaves of sets, it is invertible on abelian sheaves. -/
theorem isIso_etaleAbelianBaseChange_of_isIso_smallEtaleSetBaseChange
    (hs : IsIso (smallEtaleSetBaseChange.{u, 0} g' f' f g h)) :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' h) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun M ↦
    (isIso_etaleAbelianBaseChange_app_iff f g g' f' h M).2 (NatIso.isIso_app_of_isIso _ _)

end Cube

end Forget

section FreeEqualizer

/-- **A set is the equalizer of the two maps `ℤ[S] ⇉ ℤ[ℤ[S]]`**, `x ↦ [x]` and the image of
`s ↦ [s]` under `ℤ[-]`: an element on which they agree is a generator. -/
lemma FreeAbelianGroup.exists_of_eq_of_of_eq_map {S : Type*} (x : FreeAbelianGroup S)
    (h : FreeAbelianGroup.of x = FreeAbelianGroup.map FreeAbelianGroup.of x) :
    ∃ s, FreeAbelianGroup.of s = x := by
  by_contra hne
  push Not at hne
  have h0 : (FreeAbelianGroup.coeff x).comp (FreeAbelianGroup.map FreeAbelianGroup.of) = 0 := by
    refine FreeAbelianGroup.lift_ext _ _ fun s ↦ ?_
    simp [FreeAbelianGroup.coeff, hne s]
  have h1 := congrArg (FreeAbelianGroup.coeff x) h
  have h2 : FreeAbelianGroup.coeff x (FreeAbelianGroup.map FreeAbelianGroup.of x) = 0 := by
    rw [← AddMonoidHom.comp_apply, h0, AddMonoidHom.zero_apply]
  rw [h2] at h1
  simp [FreeAbelianGroup.coeff] at h1

variable {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Type (u + 1))

/-- The free abelian presheaf on a presheaf of sets. -/
abbrev freePresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} := P ⋙ AddCommGrpCat.free

/-- The inclusion of a presheaf of sets in its free abelian presheaf. -/
def freePresheafι : P ⟶ freePresheaf P ⋙ forget AddCommGrpCat.{u + 1} where
  app U := TypeCat.ofHom fun s ↦ FreeAbelianGroup.of s
  naturality U V a := by
    ext s
    exact (FreeAbelianGroup.map_of_apply s).symm

/-- The first of the two maps `ℤ[P] ⇉ ℤ[ℤ[P]]`: a section goes to the generator it names. -/
def freePresheafFst :
    freePresheaf P ⋙ forget AddCommGrpCat.{u + 1} ⟶
      freePresheaf (freePresheaf P ⋙ forget AddCommGrpCat.{u + 1}) ⋙
        forget AddCommGrpCat.{u + 1} where
  app U := TypeCat.ofHom fun x ↦ FreeAbelianGroup.of x
  naturality U V a := by
    ext x
    exact (FreeAbelianGroup.map_of_apply x).symm

/-- The second of the two maps `ℤ[P] ⇉ ℤ[ℤ[P]]`: `ℤ[-]` applied to the inclusion of `P`. -/
def freePresheafSnd :
    freePresheaf P ⋙ forget AddCommGrpCat.{u + 1} ⟶
      freePresheaf (freePresheaf P ⋙ forget AddCommGrpCat.{u + 1}) ⋙
        forget AddCommGrpCat.{u + 1} :=
  Functor.whiskerRight (Functor.whiskerRight (freePresheafι P) AddCommGrpCat.free)
    (forget AddCommGrpCat.{u + 1})

/-- The inclusion `P ⟶ ℤ[P]` equalizes the two maps `ℤ[P] ⇉ ℤ[ℤ[P]]`. -/
lemma freePresheafι_condition :
    freePresheafι P ≫ freePresheafFst P = freePresheafι P ≫ freePresheafSnd P := by
  ext U s
  exact (FreeAbelianGroup.map_of_apply s).symm

/-- **A presheaf of sets is the equalizer of `ℤ[P] ⇉ ℤ[ℤ[P]]`**, sectionwise. -/
def isLimitFreePresheafFork :
    IsLimit (Fork.ofι (freePresheafι P) (freePresheafι_condition P)) := by
  refine evaluationJointlyReflectsLimits _ fun U ↦ ?_
  refine (isLimitMapConeForkEquiv ((evaluation Cᵒᵖ (Type (u + 1))).obj U)
    (freePresheafι_condition P)).symm ?_
  refine Classical.choice ((Types.type_equalizer_iff_unique _ _).2 fun x hx ↦ ?_)
  obtain ⟨s, hs⟩ := FreeAbelianGroup.exists_of_eq_of_of_eq_map x hx
  refine ⟨s, hs, fun t ht ↦ FreeAbelianGroup.of_injective (ht.trans hs.symm)⟩

end FreeEqualizer

section EqualizerTransfer

/-- **A natural transformation between functors preserving equalizers is invertible at an
equalizer as soon as it is invertible at the two objects of the parallel pair.** -/
lemma isIso_app_of_isLimit_fork {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {Φ Ψ : 𝒞 ⥤ 𝒟}
    [PreservesLimitsOfShape WalkingParallelPair Φ] [PreservesLimitsOfShape WalkingParallelPair Ψ]
    (β : Φ ⟶ Ψ) {X Y Z : 𝒞} {ι : X ⟶ Y} {a b : Y ⟶ Z} (w : ι ≫ a = ι ≫ b)
    (hl : IsLimit (Fork.ofι ι w)) [IsIso (β.app Y)] [IsIso (β.app Z)] : IsIso (β.app X) := by
  have hΦ := isLimitMapConeForkEquiv Φ w (isLimitOfPreserves Φ hl)
  have hΨ := isLimitMapConeForkEquiv Ψ w (isLimitOfPreserves Ψ hl)
  have hk : (Ψ.map ι ≫ inv (β.app Y)) ≫ Φ.map a = (Ψ.map ι ≫ inv (β.app Y)) ≫ Φ.map b := by
    have hc (c : Y ⟶ Z) : inv (β.app Y) ≫ Φ.map c = Ψ.map c ≫ inv (β.app Z) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, ← β.naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    rw [Category.assoc, Category.assoc, hc, hc, ← Category.assoc, ← Category.assoc,
      ← Ψ.map_comp, ← Ψ.map_comp, w]
  let k : Ψ.obj X ⟶ Φ.obj X := Fork.IsLimit.lift hΦ (Ψ.map ι ≫ inv (β.app Y)) hk
  have hkι : k ≫ Φ.map ι = Ψ.map ι ≫ inv (β.app Y) := Fork.IsLimit.lift_ι hΦ
  refine ⟨k, ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext hΦ ?_
    change (β.app X ≫ k) ≫ Φ.map ι = 𝟙 _ ≫ Φ.map ι
    rw [Category.assoc, hkι, ← Category.assoc, ← β.naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · refine Fork.IsLimit.hom_ext hΨ ?_
    change (k ≫ β.app X) ≫ Ψ.map ι = 𝟙 _ ≫ Ψ.map ι
    rw [Category.assoc, ← β.naturality, ← Category.assoc, hkι, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- **Inverse image of sheaves of sets on small étale sites is left exact.** The left Kan
extension is computed pointwise as a colimit over a filtered costructured-arrow category, and
filtered colimits of sets commute with finite limits; sheafification is left exact. -/
instance smallEtaleInverseImage_preservesFiniteLimits {S T : Scheme.{u}} (k : T ⟶ S) :
    PreservesFiniteLimits (smallEtaleInverseImage.{u, 0} k) := by
  let G := smallEtaleBaseChange k
  have : PreservesFiniteLimits
      (G.op.lan : (S.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ _) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation _ J
    intro K
    have : IsFiltered (CostructuredArrow G.op K) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G K.unop)
    exact preservesLimitsOfShape_of_natIso
      (Stacks.Topology.lanCompEvaluationIsoColim (Type (u + 1)) G.op K).symm
  change PreservesFiniteLimits (sheafToPresheaf (Scheme.smallEtaleTopology S) (Type (u + 1)) ⋙
    G.op.lan ⋙ presheafToSheaf (Scheme.smallEtaleTopology T) (Type (u + 1)))
  infer_instance

end EqualizerTransfer

section SetFromAbelian

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- Sheafifying a presheaf of sets underlying an abelian presheaf gives the sheaf of sets
underlying the abelian sheafification. -/
abbrev sheafifyForgetIso {S : Scheme.{u}} (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (presheafToSheaf S.smallEtaleTopology (Type (u + 1))).obj (Q ⋙ forget AddCommGrpCat.{u + 1}) ≅
      (etaleForget S).obj ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj Q) :=
  (sheafComposeNatIso S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (sheafificationAdjunction S.smallEtaleTopology (Type (u + 1)))).app Q

/-- **Transport of base change from abelian sheaves to sheaves of sets.** If the base change map
of a commutative square is invertible on abelian sheaves, it is invertible on sheaves of sets.

A sheaf of sets `P` is the equalizer of the two maps `ℤ[P] ⇉ ℤ[ℤ[P]]` of sheaves of sets
underlying abelian sheaves (sheafify the sectionwise equalizer of presheaves; sheafification is
left exact and commutes with forgetting the group structure). Both composites
`g^{-1} f_*` and `f'_* (g')^{-1}` preserve equalizers, and the set base change map is invertible
at sheaves underlying abelian sheaves by
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_app_iff`. -/
theorem isIso_smallEtaleSetBaseChange_of_isIso_etaleAbelianBaseChange
    (hab : IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' h)) :
    IsIso (smallEtaleSetBaseChange.{u, 0} g' f' f g h) := by
  have : PreservesLimitsOfShape WalkingParallelPair (smallEtalePushforward f (Type (u + 1))) :=
    (smallEtaleInverseImageAdjunction.{u, 0} f).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : PreservesLimitsOfShape WalkingParallelPair (smallEtalePushforward f' (Type (u + 1))) :=
    (smallEtaleInverseImageAdjunction.{u, 0} f').rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : PreservesLimitsOfShape WalkingParallelPair
      (smallEtalePushforward f (Type (u + 1)) ⋙ smallEtaleInverseImage.{u, 0} g) := inferInstance
  have : PreservesLimitsOfShape WalkingParallelPair
      (smallEtaleInverseImage.{u, 0} g' ⋙ smallEtalePushforward f' (Type (u + 1))) :=
    inferInstance
  have hU : ∀ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso ((smallEtaleSetBaseChange.{u, 0} g' f' f g h).app ((etaleForget X).obj A)) :=
    fun A ↦ (isIso_etaleAbelianBaseChange_app_iff f g g' f' h A).1
      (NatIso.isIso_app_of_isIso _ _)
  refine (NatTrans.isIso_iff_isIso_app _).2 fun P ↦ ?_
  let Pp := P.obj
  have hl := isLimitMapConeForkEquiv (presheafToSheaf X.smallEtaleTopology (Type (u + 1)))
    (freePresheafι_condition Pp)
    (isLimitOfPreserves (presheafToSheaf X.smallEtaleTopology (Type (u + 1)))
      (isLimitFreePresheafFork Pp))
  have h₁ := (NatTrans.isIso_app_iff_of_iso (smallEtaleSetBaseChange.{u, 0} g' f' f g h)
    (sheafifyForgetIso (freePresheaf Pp)).symm).1 (hU _)
  have h₂ := (NatTrans.isIso_app_iff_of_iso (smallEtaleSetBaseChange.{u, 0} g' f' f g h)
    (sheafifyForgetIso (freePresheaf (freePresheaf Pp ⋙ forget AddCommGrpCat.{u + 1})))).2
      (hU _)
  have h₃ := isIso_app_of_isLimit_fork (smallEtaleSetBaseChange.{u, 0} g' f' f g h) _ hl
  exact (NatTrans.isIso_app_iff_of_iso (smallEtaleSetBaseChange.{u, 0} g' f' f g h)
    (sheafificationIso P).symm).1 h₃

end SetFromAbelian

section StalkTransfer

/-- **Inverse image of abelian sheaves inverts a morphism exactly when inverse image of sheaves of
sets inverts the underlying morphism of sheaves of sets.** -/
theorem isIso_etaleAbelianInverseImage_map_iff {S T : Scheme.{u}} (k : T ⟶ S)
    {A B : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (m : A ⟶ B) :
    IsIso ((etaleAbelianInverseImage.{u, 0} k).map m) ↔
      IsIso ((smallEtaleInverseImage.{u, 0} k).map ((etaleForget S).map m)) := by
  have hn := (etaleForgetPullback k).naturality m
  rw [← isIso_iff_of_reflects_iso _ (etaleForget T)]
  change IsIso ((etaleForget T).map ((etaleAbelianInverseImage.{u, 0} k).map m)) ↔ _
  rw [← isIso_comp_left_iff ((etaleForgetPullback k).app A)]
  change IsIso (_ ≫ ((etaleAbelianInverseImage.{u, 0} k ⋙ etaleForget T).map m)) ↔ _
  rw [← hn]
  exact isIso_comp_right_iff _ _

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **Transport of base change after an inverse image, from sheaves of sets to abelian sheaves.**
For a commutative square and any `k : T ⟶ Y'`, if `k^{-1}` inverts the set base change map at
the underlying sheaf of sets of an abelian sheaf `M`, then `k^{-1}` inverts the abelian base
change map at `M`. With `k` a geometric point this transports a statement about stalks. -/
theorem isIso_etaleAbelianInverseImage_map_etaleAbelianBaseChange_app {T : Scheme.{u}}
    (k : T ⟶ Y') (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hs : IsIso ((smallEtaleInverseImage.{u, 0} k).map
      ((smallEtaleSetBaseChange.{u, 0} g' f' f g h).app ((etaleForget X).obj M)))) :
    IsIso ((etaleAbelianInverseImage.{u, 0} k).map
      ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app M)) := by
  have : IsIso ((smallEtaleInverseImage.{u, 0} k).map
      ((smallEtalePushforward f' (Type (u + 1))).map ((etaleForgetPullback g').app M))) :=
    inferInstance
  have key := ((smallEtaleInverseImage.{u, 0} k).map_comp _ _).symm.trans
    ((congrArg (smallEtaleInverseImage.{u, 0} k).map
      (forget_etaleAbelianBaseChange_app f g g' f' h M)).trans
      ((smallEtaleInverseImage.{u, 0} k).map_comp
        ((smallEtaleSetBaseChange.{u, 0} g' f' f g h).app ((etaleForget X).obj M))
        ((smallEtalePushforward f' (Type (u + 1))).map ((etaleForgetPullback g').app M))))
  rw [isIso_etaleAbelianInverseImage_map_iff,
    ← isIso_comp_left_iff ((smallEtaleInverseImage.{u, 0} k).map
      ((etaleForgetPullback g).app ((etaleAbelianDirectImage.{u, 0} f).obj M))), key]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hs this

end StalkTransfer

end Stacks.EtaleCohomology

end
