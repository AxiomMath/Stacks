module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.RanBaseChangeMate
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MateUnderlying
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# Beck–Chevalley for the degreewise square of a morphism of simplicial sites

The square of topoi of Stacks 0D96 attached to a morphism between simplicial sites in the
cocontinuous case carries two 2-cells: the comparison
`CategoryTheory.CocontinuousSimplicialSite.Morphism.totalComponentPushforwardIso` of the two
composite direct images, and its mate for the two adjunctions of the component inclusions. The mate
of an isomorphism is in general only a morphism; this file proves that this one is invertible.

## Main results

* `CategoryTheory.cocontinuousPushforwardIsoOfEq_inv_app_hom`: the transport of a direct image
  along an equality of cocontinuous site functors is, on underlying presheaves, the conjugate of
  the corresponding transport of precompositions.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalComponentPushforwardIso_inv_app_hom`:
  on underlying presheaves the comparison of Stacks 0D96 is the comparison of the two composite
  right Kan extensions.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.isIso_totalComponentPushforward_mate`:
  **the Beck–Chevalley statement**, that the mate of that comparison is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare Stacks.CategoryTheory
open Opposite

universe u

namespace CategoryTheory

section Congr

variable {A B E F : Type*} [Category A] [Category B] [Category E] [Category F]
  {G : A ⥤ E} {Hh : B ⥤ F} {L₁ L₂ : A ⥤ B} {R : B ⥤ A} {L₃ L₄ : E ⥤ F} {R₃ : F ⥤ E}

/-- **Invertibility of a mate does not depend on which adjunctions are used**: if the mate of `β`
for adjunctions `L₂ ⊣ R` and `L₄ ⊣ R₃` is invertible, so is its mate for any adjunctions `L₁ ⊣ R`
and `L₃ ⊣ R₃` with the same right adjoints. -/
theorem isIso_mateEquiv_symm_congr (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₃) (β : TwoSquare R Hh G R₃)
    (hiso : IsIso ((mateEquiv adj₂ adj₄).symm β).natTrans) :
    IsIso ((mateEquiv adj₁ adj₃).symm β).natTrans := by
  rw [Stacks.CategoryTheory.mateEquiv_symm_congr_left adj₁ adj₂ adj₃ β,
    Stacks.CategoryTheory.mateEquiv_symm_congr_right adj₂ adj₄ adj₃ β]
  show IsIso ((Functor.whiskerLeft G (Adjunction.leftAdjointUniq adj₃ adj₄).hom ≫
    ((mateEquiv adj₂ adj₄).symm β).natTrans) ≫
    Functor.whiskerRight (Adjunction.leftAdjointUniq adj₂ adj₁).hom Hh)
  infer_instance

end Congr

section Transport

variable {Cc Ee : Type u} [SmallCategory Cc] [SmallCategory Ee]
  (J : GrothendieckTopology Cc) (L : GrothendieckTopology Ee)

/-- The transport of a direct image along an equality of cocontinuous site functors acts on
underlying presheaves as the conjugate, for the two right Kan extension adjunctions, of the
transport of the precomposition functors along that equality. -/
theorem cocontinuousPushforwardIsoOfEq_inv_app_hom {F G : Cc ⥤ Ee}
    [F.IsCocontinuous J L] [G.IsCocontinuous J L] (e : F = G) (X : Sheaf J (Type u)) :
    ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J L
        e).inv.app X).hom =
      (conjugateEquiv (G.op.ranAdjunction (Type u)) (F.op.ranAdjunction (Type u))
        ((whiskeringLeft Ccᵒᵖ Eeᵒᵖ (Type u)).map
          (eqToHom (congrArg Functor.op e)))).app X.obj := by
  cases e
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  simp
  rfl

/-- The presheaf-level compositor of direct images along cocontinuous site functors is the
comparison of the two right adjoints of the composite precomposition. -/
theorem ranOpCompIso_eq_ranCompIsoOfAdjunctions {Aa Bb Dd : Type u} [SmallCategory Aa]
    [SmallCategory Bb] [SmallCategory Dd] (a : Aa ⥤ Bb) (b : Bb ⥤ Dd) :
    _root_.ranOpCompIso a b = Functor.ranCompIsoOfAdjunctions (Type u) a.op b.op := by
  rw [ranOpCompIso_def]
  rfl

/-- **The composite comparison of direct images attached to a commuting square of cocontinuous
site functors is, on underlying presheaves, the comparison of the two composite right Kan
extensions.**

The square commutes on the nose, `i ⋙ V = v ⋙ i'`, and `w` is a 2-cell of the square whose
opposite is the transport along that equality. -/
theorem compIso_inv_app_hom_eq_ranCompSquare
    {Cn Ct Cn' Ct' : Type u} [SmallCategory Cn] [SmallCategory Ct] [SmallCategory Cn']
    [SmallCategory Ct'] (Jn : GrothendieckTopology Cn) (K : GrothendieckTopology Ct)
    (Jn' : GrothendieckTopology Cn') (K' : GrothendieckTopology Ct')
    (i : Cn ⥤ Ct) (i' : Cn' ⥤ Ct') (v : Cn ⥤ Cn') (V : Ct ⥤ Ct')
    [i.IsCocontinuous Jn K] [i'.IsCocontinuous Jn' K'] [v.IsCocontinuous Jn Jn']
    [V.IsCocontinuous K K'] [(i ⋙ V).IsCocontinuous Jn K'] [(v ⋙ i').IsCocontinuous Jn K']
    (e : i ⋙ V = v ⋙ i') (w : TwoSquare i v V i')
    (hw : w.op.natTrans = eqToHom (congrArg Functor.op e.symm)) (Z : Sheaf Jn (Type u)) :
    ((sheafPushforwardCocontinuousCompIso Jn K K' i V).inv.app Z).hom ≫
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jn K'
          e.symm).inv.app Z).hom ≫
        ((sheafPushforwardCocontinuousCompIso Jn Jn' K' v i').hom.app Z).hom =
      (ranCompSquare (Type u) w.op).natTrans.app Z.obj := by
  have hS := (Iso.eq_inv_comp _).mpr (ranCompIso_hom_comp_ranCompSquare (H := Type u) w.op)
  rw [sheafPushforwardCocontinuousCompIso_inv_app_hom,
    cocontinuousPushforwardIsoOfEq_inv_app_hom,
    sheafPushforwardCocontinuousCompIso_hom_app_hom,
    ranOpCompIso_eq_ranCompIsoOfAdjunctions, ranOpCompIso_eq_ranCompIsoOfAdjunctions,
    hS, hw]
  simp only [NatTrans.comp_app]
  rfl

end Transport

namespace CocontinuousSimplicialSite.Morphism

variable {C C' : CocontinuousSimplicialSite.{u}} (h : Morphism C C') (n : SimplexCategory)

/-- The square formed by the two component inclusions of simplicial degree `n`, the degreewise
functor and the total functor. -/
abbrev inclusionSquare :
    TwoSquare (Grothendieck.ι C.underlying (op n)) (h.hom.app (op n)).toFunctor h.totalFunctor
      (Grothendieck.ι C'.underlying (op n)) :=
  (Grothendieck.ιCompMap h.hom (op n)).hom

/-- The square of component inclusions is Guitart exact. -/
instance guitartExact_inclusionSquare : (inclusionSquare h n).GuitartExact :=
  Grothendieck.guitartExact_ιCompMap h.hom (op n)

/-- The opposite of the square of component inclusions is Guitart exact. -/
instance guitartExact_inclusionSquare_op : (inclusionSquare h n).op.GuitartExact :=
  inferInstance

/-- The 2-cell of the opposite square of component inclusions is the transport along the equality
of site functors it comes from. -/
theorem inclusionSquare_op_natTrans :
    (inclusionSquare h n).op.natTrans =
      eqToHom (congrArg Functor.op (h.ι_comp_totalFunctor (op n)).symm) := by
  refine NatTrans.ext (funext fun X => ?_)
  exact ((eqToHom_app (congrArg Functor.op (h.ι_comp_totalFunctor (op n)).symm) X).trans
    (eqToHom_refl _ _)).symm

/-- **On underlying presheaves the comparison of Stacks 0D96 is the comparison of the two
composite right Kan extensions.** -/
theorem totalComponentPushforwardIso_inv_app_hom
    (Z : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u)) :
    ((h.totalComponentPushforwardIso n).inv.app Z).hom =
      (ranCompSquare (Type u) (inclusionSquare h n).op).natTrans.app Z.obj := by
  let iv : ((h.hom.app (op n)).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n))) (topologyOfCoverings (C'.coverage (op n))) :=
    h.isCocontinuous (op n)
  let ii : (Grothendieck.ι C.underlying (op n)).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  let ii' : (Grothendieck.ι C'.underlying (op n)).IsCocontinuous
      (topologyOfCoverings (C'.coverage (op n)))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  let iV := h.totalFunctor_isCocontinuous
  let ivi' : ((h.hom.app (op n)).toFunctor ⋙ Grothendieck.ι C'.underlying (op n)).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (topologyOfCoverings (C'.coverage (op n)))
  let iiV : (Grothendieck.ι C.underlying (op n) ⋙ h.totalFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    CategoryTheory.isCocontinuous_comp _ _ _
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
  exact compIso_inv_app_hom_eq_ranCompSquare
    (topologyOfCoverings (C.coverage (op n)))
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
    (topologyOfCoverings (C'.coverage (op n)))
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage)
    _ _ _ _ (h.ι_comp_totalFunctor (op n)) (inclusionSquare h n)
    (inclusionSquare_op_natTrans h n) Z

/-- **Stacks 0D96, the Beck–Chevalley statement for the degreewise square.** The mate of the
comparison of the two composite direct images is invertible. -/
theorem isIso_totalComponentPushforward_mate :
    IsIso ((mateEquiv
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).adj
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).adj).symm
      (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv)).natTrans := by
  let ic : (Grothendieck.ι C.underlying (op n)).IsContinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  let icc : (Grothendieck.ι C.underlying (op n)).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  let ic' : (Grothendieck.ι C'.underlying (op n)).IsContinuous
      (topologyOfCoverings (C'.coverage (op n)))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  let icc' : (Grothendieck.ι C'.underlying (op n)).IsCocontinuous
      (topologyOfCoverings (C'.coverage (op n)))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  let ivr : ((h.hom.app (op n)).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (topologyOfCoverings (C'.coverage (op n))) := h.isCocontinuous (op n)
  let iVr : h.totalFunctor.IsCocontinuous
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    h.totalFunctor_isCocontinuous
  have key : IsIso ((mateEquiv
      ((Grothendieck.ι C.underlying (op n)).sheafAdjunctionCocontinuous (Type u)
          (topologyOfCoverings (C.coverage (op n)))
          (SimplicialCoverings.totalTopology C.underlying C.coverage))
      ((Grothendieck.ι C'.underlying (op n)).sheafAdjunctionCocontinuous (Type u)
          (topologyOfCoverings (C'.coverage (op n)))
          (SimplicialCoverings.totalTopology C'.underlying C'.coverage))).symm
      (TwoSquare.mk
        ((Grothendieck.ι C.underlying (op n)).sheafPushforwardCocontinuous (Type u)
          (topologyOfCoverings (C.coverage (op n)))
          (SimplicialCoverings.totalTopology C.underlying C.coverage))
        (((h.hom.app (op n)).toFunctor).sheafPushforwardCocontinuous (Type u)
          (topologyOfCoverings (C.coverage (op n)))
          (topologyOfCoverings (C'.coverage (op n))))
        (h.totalFunctor.sheafPushforwardCocontinuous (Type u)
          (SimplicialCoverings.totalTopology C.underlying C.coverage)
          (SimplicialCoverings.totalTopology C'.underlying C'.coverage))
        ((Grothendieck.ι C'.underlying (op n)).sheafPushforwardCocontinuous (Type u)
          (topologyOfCoverings (C'.coverage (op n)))
          (SimplicialCoverings.totalTopology C'.underlying C'.coverage))
        (h.totalComponentPushforwardIso n).inv)).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    refine (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ (Type u))).mp ?_
    rw [ObjectProperty.ι_map]
    rw [@mateEquiv_symm_sheafAdjunctionCocontinuous_app_hom _ _ _ _ _ _ _ _ _ _ _ _
      (Grothendieck.ι C.underlying (op n)) ic icc
      (Grothendieck.ι C'.underlying (op n)) ic' icc'
      (h.hom.app (op n)).toFunctor ivr h.totalFunctor iVr _
      (ranCompSquare (Type u) (inclusionSquare h n).op)
      (fun Z => totalComponentPushforwardIso_inv_app_hom h n Z) Y,
      NatTrans.congr_app (mateEquiv_symm_ranCompSquare (H := Type u)
        (inclusionSquare h n).op) Y.obj]
    have : h.totalFunctor.op.HasPointwiseRightKanExtension Y.obj := fun _ => inferInstance
    exact TwoSquare.isIso_ranBaseChange_app (inclusionSquare h n).op Y.obj
  exact isIso_mateEquiv_symm_congr _ _ _ _ _ key

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end
