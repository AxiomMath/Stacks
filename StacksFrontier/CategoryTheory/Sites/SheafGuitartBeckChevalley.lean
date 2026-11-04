module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Beck–Chevalley for a Guitart exact square of sites, with arbitrary coefficients

Consider a square of functors of sites
```
C₁ --v--> C₂
|  i      |  j
C₃ --w--> C₄
```
with a 2-cell `q : v ⋙ j ⟶ i ⋙ w`, where `v` and `w` are continuous and the vertical functors
`i`, `j` are both continuous and cocontinuous. Restriction along `i` is left adjoint to the direct
image along the cocontinuous functor `i`, a right Kan extension, and likewise for `j`. When `q` is
Guitart exact, the base change of right Kan extensions along the opposite square is invertible,
which gives an isomorphism of direct images `v_* ⋙ i_* ≅ j_* ⋙ w_*`; its mate along the two
restrictions is a comparison

`w_* ⋙ i^{-1} ⟶ j^{-1} ⋙ v_*`

which, on underlying presheaves, is restriction along `q`. For any adjunctions `L ⊣ w_*` and
`L' ⊣ v_*` its mate along them is the Beck–Chevalley comparison

`i^{-1} ⋙ L' ⟶ L ⋙ j^{-1}`

of the inverse images, and by the iterated mate theorem that comparison is the conjugate of the
isomorphism of direct images, hence an isomorphism. This is the argument by which the inverse
image along a total site is computed degreewise (Stacks 0D96), here for sheaves with values in an
arbitrary category `A` with the right Kan extensions needed, such as abelian groups.

## Main definitions

* `CategoryTheory.TwoSquare.sheafRanBaseChangeIso`: the square of direct images
  `v_* ⋙ i_* ≅ j_* ⋙ w_*`.
* `CategoryTheory.TwoSquare.sheafRestrictionSquare`: its mate `w_* ⋙ i^{-1} ⟶ j^{-1} ⋙ v_*`.
* `CategoryTheory.TwoSquare.sheafBeckChevalley`: the Beck–Chevalley comparison of the inverse
  images.

## Main results

* `CategoryTheory.TwoSquare.sheafRestrictionSquare_app_hom`: on underlying presheaves the mate of
  the square of direct images is restriction along `q`.
* `CategoryTheory.TwoSquare.isIso_sheafRestrictionSquare`: it is invertible when `q` is.
* `CategoryTheory.TwoSquare.isIso_sheafBeckChevalley`: the Beck–Chevalley comparison is
  invertible.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoSquare

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃) (J₄ : GrothendieckTopology C₄)
  {v : C₁ ⥤ C₂} {i : C₁ ⥤ C₃} {j : C₂ ⥤ C₄} {w : C₃ ⥤ C₄} (q : TwoSquare v i j w)
  (A : Type*) [Category* A]
  [v.IsContinuous J₁ J₂] [w.IsContinuous J₃ J₄] [i.IsContinuous J₁ J₃] [i.IsCocontinuous J₁ J₃]
  [j.IsContinuous J₂ J₄] [j.IsCocontinuous J₂ J₄]
  [∀ F : C₁ᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
  [∀ F : C₂ᵒᵖ ⥤ A, j.op.HasPointwiseRightKanExtension F]

/-- The square of direct images `v_* ⋙ i_* ≅ j_* ⋙ w_*` attached to a Guitart exact square of
site functors with continuous horizontal and cocontinuous vertical functors: the base change of
right Kan extensions along the opposite square, read on sheaves. -/
def sheafRanBaseChangeIso [q.GuitartExact] :
    v.sheafPushforwardContinuous A J₁ J₂ ⋙ i.sheafPushforwardCocontinuous A J₁ J₃ ≅
      j.sheafPushforwardCocontinuous A J₂ J₄ ⋙ w.sheafPushforwardContinuous A J₃ J₄ :=
  (Functor.fullyFaithfulCancelRight (sheafToPresheaf J₃ A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J₂ A)
      (asIso (q.op.ranBaseChange (D := A))))).symm

omit [i.IsContinuous J₁ J₃] [j.IsContinuous J₂ J₄] in
/-- On underlying presheaves, the inverse of the square of direct images is the base change of
right Kan extensions. -/
theorem sheafRanBaseChangeIso_inv_app_hom [q.GuitartExact] (G : Sheaf J₂ A) :
    ((sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv.app G).hom =
      q.op.ranBaseChange.app G.obj :=
  (sheafToPresheaf J₃ A).map_preimage _

/-- The mate `w_* ⋙ i^{-1} ⟶ j^{-1} ⋙ v_*` of the square of direct images along the
adjunctions `i^{-1} ⊣ i_*` and `j^{-1} ⊣ j_*`. -/
abbrev sheafRestrictionSquare [q.GuitartExact] :
    TwoSquare (w.sheafPushforwardContinuous A J₃ J₄) (j.sheafPushforwardContinuous A J₂ J₄)
      (i.sheafPushforwardContinuous A J₁ J₃) (v.sheafPushforwardContinuous A J₁ J₂) :=
  (mateEquiv (j.sheafAdjunctionCocontinuous A J₂ J₄)
    (i.sheafAdjunctionCocontinuous A J₁ J₃)).symm
    (TwoSquare.mk _ _ _ _ (sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv)

/-- **On underlying presheaves, the mate of the square of direct images is restriction along the
square of site functors.** -/
theorem sheafRestrictionSquare_app_hom [q.GuitartExact] (F : Sheaf J₄ A) :
    ((sheafRestrictionSquare J₁ J₂ J₃ J₄ q A).natTrans.app F).hom =
      Functor.whiskerRight q.op.natTrans F.obj := by
  have hR : ∀ {X : C₁ᵒᵖ ⥤ A} {Y : C₃ᵒᵖ ⥤ A} (y : i.op ⋙ Y ⟶ X),
      Functor.whiskerLeft i.op ((i.op.ranAdjunction A).homEquiv Y X y) ≫
        (i.op.ranAdjunction A).counit.app X = y := by
    intro X Y y
    have h := (i.op.ranAdjunction A).homEquiv_counit
      (g := (i.op.ranAdjunction A).homEquiv Y X y)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hε : ∀ G : Sheaf J₁ A,
      ((i.sheafAdjunctionCocontinuous A J₁ J₃).counit.app G).hom =
        (i.op.ranAdjunction A).counit.app G.obj :=
    Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _
  have hη : ((j.sheafAdjunctionCocontinuous A J₂ J₄).unit.app F).hom =
      (j.op.ranAdjunction A).unit.app F.obj :=
    Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ F
  have e0 : (sheafRestrictionSquare J₁ J₂ J₃ J₄ q A).natTrans.app F =
      (i.sheafPushforwardContinuous A J₁ J₃).map ((w.sheafPushforwardContinuous A J₃ J₄).map
        ((j.sheafAdjunctionCocontinuous A J₂ J₄).unit.app F)) ≫
      (i.sheafPushforwardContinuous A J₁ J₃).map ((sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv.app
        ((j.sheafPushforwardContinuous A J₂ J₄).obj F)) ≫
      (i.sheafAdjunctionCocontinuous A J₁ J₃).counit.app ((v.sheafPushforwardContinuous A J₁ J₂).obj
        ((j.sheafPushforwardContinuous A J₂ J₄).obj F)) := by
    simp [sheafRestrictionSquare, mateEquiv]
  rw [e0]
  show Functor.whiskerLeft i.op (Functor.whiskerLeft w.op
      ((j.sheafAdjunctionCocontinuous A J₂ J₄).unit.app F).hom) ≫
    Functor.whiskerLeft i.op ((sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv.app
      ((j.sheafPushforwardContinuous A J₂ J₄).obj F)).hom ≫
    ((i.sheafAdjunctionCocontinuous A J₁ J₃).counit.app
      ((v.sheafPushforwardContinuous A J₁ J₂).obj
        ((j.sheafPushforwardContinuous A J₂ J₄).obj F))).hom = _
  rw [hη, sheafRanBaseChangeIso_inv_app_hom, hε]
  have hB : Functor.whiskerLeft i.op (q.op.ranBaseChange.app (j.op ⋙ F.obj)) ≫
      (i.op.ranAdjunction A).counit.app (v.op ⋙ j.op ⋙ F.obj) =
      ((Functor.RightExtension.mk _ (j.op.ranCounit.app (j.op ⋙ F.obj))).compTwoSquare
        q.op).hom :=
    hR _
  show Functor.whiskerLeft i.op (Functor.whiskerLeft w.op
      ((j.op.ranAdjunction A).unit.app F.obj)) ≫
    (Functor.whiskerLeft i.op (q.op.ranBaseChange.app (j.op ⋙ F.obj)) ≫
      (i.op.ranAdjunction A).counit.app (v.op ⋙ j.op ⋙ F.obj)) = _
  rw [hB]
  refine NatTrans.ext (funext fun X => ?_)
  have n1 : ((j.op.ranAdjunction A).unit.app F.obj).app (w.op.obj (i.op.obj X)) ≫
      (j.op.ran.obj (j.op ⋙ F.obj)).map (q.op.natTrans.app X) =
      F.obj.map (q.op.natTrans.app X) ≫
        ((j.op.ranAdjunction A).unit.app F.obj).app (j.op.obj (v.op.obj X)) :=
    (((j.op.ranAdjunction A).unit.app F.obj).naturality (q.op.natTrans.app X)).symm
  have t1 := Functor.ranCounit_app_app_ranAdjunction_unit_app_app j.op F.obj (v.op.obj X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  show ((j.op.ranAdjunction A).unit.app F.obj).app (w.op.obj (i.op.obj X)) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight q.op.natTrans (j.op.ran.obj (j.op ⋙ F.obj)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft v.op (j.op.ranCounit.app (j.op ⋙ F.obj))).app X = _
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rw [reassoc_of% n1, t1]
  exact Category.comp_id _

/-- The mate of the square of direct images is an isomorphism as soon as the square of site
functors is. -/
instance isIso_sheafRestrictionSquare [q.GuitartExact] [IsIso q.natTrans] :
    IsIso (sheafRestrictionSquare J₁ J₂ J₃ J₄ q A).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← ObjectProperty.isIso_hom_iff, sheafRestrictionSquare_app_hom]
  have : IsIso q.op.natTrans := by
    change IsIso (NatTrans.op q.natTrans)
    infer_instance
  exact (Functor.isoWhiskerRight (asIso q.op.natTrans) F.obj).isIso_hom

variable {J₁ J₂ J₃ J₄ A}
variable {L : Sheaf J₃ A ⥤ Sheaf J₄ A} {L' : Sheaf J₁ A ⥤ Sheaf J₂ A}
  (adj : L ⊣ w.sheafPushforwardContinuous A J₃ J₄)
  (adj' : L' ⊣ v.sheafPushforwardContinuous A J₁ J₂)

variable (J₁ J₂ J₃ J₄) in
/-- **The Beck–Chevalley comparison of the inverse images**: the comparison
`i^{-1} ⋙ L' ⟶ L ⋙ j^{-1}` between restricting along `i` and then pulling back, and pulling back
and then restricting along `j`, the mate of `sheafRestrictionSquare` along `L ⊣ w_*` and
`L' ⊣ v_*`. -/
abbrev sheafBeckChevalley [q.GuitartExact] :
    TwoSquare (i.sheafPushforwardContinuous A J₁ J₃) L L' (j.sheafPushforwardContinuous A J₂ J₄) :=
  (mateEquiv adj adj').symm (sheafRestrictionSquare J₁ J₂ J₃ J₄ q A)

/-- The mate of the Beck–Chevalley comparison along `L ⊣ w_*` and `L' ⊣ v_*` is
`sheafRestrictionSquare`. -/
theorem mateEquiv_sheafBeckChevalley [q.GuitartExact] :
    mateEquiv adj adj' (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj') =
      sheafRestrictionSquare J₁ J₂ J₃ J₄ q A :=
  Equiv.apply_symm_apply _ _

/-- **Beck–Chevalley.** The comparison `i^{-1} ⋙ L' ⟶ L ⋙ j^{-1}` is an isomorphism: by the
iterated mate theorem its conjugate along the composite adjunctions is the inverse of the square
of direct images, which is invertible. -/
instance isIso_sheafBeckChevalley [q.GuitartExact] :
    IsIso (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj').natTrans := by
  let adj₃ := i.sheafAdjunctionCocontinuous A J₁ J₃
  let adj₄ := j.sheafAdjunctionCocontinuous A J₂ J₄
  have key := iterated_mateEquiv_conjugateEquiv adj adj' adj₃ adj₄
    (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj')
  have h₁ : mateEquiv adj adj' (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj') =
      sheafRestrictionSquare J₁ J₂ J₃ J₄ q A :=
    Equiv.apply_symm_apply _ _
  have h₂ : mateEquiv adj₄ adj₃ (sheafRestrictionSquare J₁ J₂ J₃ J₄ q A) =
      TwoSquare.mk _ _ _ _ (sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv :=
    Equiv.apply_symm_apply _ _
  rw [h₁, h₂] at key
  have : IsIso (conjugateEquiv (adj.comp adj₄) (adj₃.comp adj')
      (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj').natTrans) := by
    rw [← key]
    exact inferInstanceAs (IsIso (sheafRanBaseChangeIso J₁ J₂ J₃ J₄ q A).inv)
  exact conjugateEquiv_of_iso (adj.comp adj₄) (adj₃.comp adj') _

/-- The Beck–Chevalley comparison, as an isomorphism. -/
def sheafBeckChevalleyIso [q.GuitartExact] :
    i.sheafPushforwardContinuous A J₁ J₃ ⋙ L' ≅ L ⋙ j.sheafPushforwardContinuous A J₂ J₄ :=
  asIso (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj').natTrans

/-- The mate of the Beck–Chevalley isomorphism is invertible. -/
instance isIso_mateEquiv_sheafBeckChevalleyIso [q.GuitartExact] [IsIso q.natTrans] :
    IsIso (mateEquiv adj adj' (sheafBeckChevalleyIso q adj adj').hom) := by
  change IsIso (mateEquiv adj adj' (sheafBeckChevalley J₁ J₂ J₃ J₄ q adj adj')).natTrans
  rw [mateEquiv_sheafBeckChevalley]
  infer_instance

end CategoryTheory.TwoSquare

end
