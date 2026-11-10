module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetBaseChangeSections

/-!
# Base change to a limit of étale neighbourhoods, on global sections

Let `(W_i)` be an inverse system of affine étale `S`-schemes over a directed set with a least
element, with limit `T` and `π : T ⟶ S`, and let `φ : A ⟶ S` be quasi-compact and quasi-separated.
For a sheaf of sets `F` on the small étale site of `A`, the base change map
`β : π⁻¹ φ_* F ⟶ (φ_T)_* p⁻¹ F` of the square of `φ` over `π`
(`Stacks.EtaleCohomology.smallEtaleSetBaseChange`) is bijective on global sections over `T`. This
is Stacks 03Q9 in degree zero for sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.EtaleLimitSections.smallEtaleSetBaseChange_limitSections`: the base
  change map intertwines the colimit descriptions of the global sections of `π⁻¹ φ_* F` and of
  `p⁻¹ F`.
* `Stacks.EtaleCohomology.EtaleLimitSections.bijective_smallEtaleSetBaseChange_app_unit`: the base
  change map is bijective on global sections over `T`.
* `Stacks.EtaleCohomology.EtaleLimitSections.isIso_Γ_map_smallEtaleSetBaseChange`: the same, as an
  isomorphism of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.EtaleLimitSections

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {S : Scheme.{u}} (W : Iᵒᵖ ⥤ S.Etale)
  (c : Cone (W ⋙ Scheme.Etale.forget S ⋙ Over.forget S)) {π : c.pt ⟶ S}
  (hπ : ∀ i, c.π.app i ≫ (W.obj i).hom = π) {A : Scheme.{u}} (φ : A ⟶ S)

/-- The morphism from the base change along `A ×_S T ⟶ T` of the final object of `T` to the final
object of `A ×_S T`. -/
def unitBaseChangeToUnit :
    (smallEtaleBaseChange (pullback.snd φ π)).obj (Scheme.Etale.mk (𝟙 c.pt)) ⟶
      Scheme.Etale.mk (𝟙 (pullback φ π)) :=
  MorphismProperty.Over.homMk (pullback.snd _ (pullback.snd φ π)) (Category.comp_id _) trivial

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- **The base change map intertwines the two colimit descriptions of global sections.** -/
theorem smallEtaleSetBaseChange_limitSections (F : Sheaf A.smallEtaleTopology (Type (u + 1)))
    (i : Iᵒᵖ) (x : F.obj.obj (op ((smallEtaleBaseChange φ).obj (W.obj i)))) :
    ((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ π) (pullback.snd φ π) φ π
        pullback.condition).app F).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
        (limitSections W c hπ (((smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
          S.smallEtaleTopology A.smallEtaleTopology).obj F) i x) =
      ((smallEtaleInverseImage.{u, 0} (pullback.fst φ π)).obj F).obj.map
          (unitBaseChangeToUnit W c φ).op
        (limitSections (baseChangeSystem W φ) (baseChangeCone W c hπ φ)
          (baseChangeCone_π_comp_hom W c hπ φ) F i x) := by
  let e := pullback.fst φ π
  let h := pullback.snd φ π
  let G := ((smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
    S.smallEtaleTopology A.smallEtaleTopology).obj F
  let P := (smallEtaleInverseImage.{u, 0} e).obj F
  let σ := smallEtaleBaseChangeLift π (W.obj i) (c.π.app i) (hπ i)
  let σ' := smallEtaleBaseChangeLift e ((baseChangeSystem W φ).obj i)
    ((baseChangeCone W c hπ φ).π.app i) (baseChangeCone_π_comp_hom W c hπ φ i)
  have hM : (smallEtaleBaseChange h).map σ ≫
      baseChangeSquareMap e h φ π pullback.condition (W.obj i) =
      unitBaseChangeToUnit W c (π := π) φ ≫ σ' := by
    apply smallEtaleBaseChange_hom_ext
    let a := ((smallEtaleBaseChange h).map σ).left
    let b := (baseChangeSquareMap e h φ π pullback.condition (W.obj i)).left
    let t := (unitBaseChangeToUnit W c (π := π) φ).left
    let d := σ'.left
    change (a ≫ b) ≫ pullback.fst (pullback.snd (W.obj i).hom φ) e =
      (t ≫ d) ≫ pullback.fst (pullback.snd (W.obj i).hom φ) e
    have hb : b ≫ pullback.fst (pullback.snd (W.obj i).hom φ) e = pullback.lift
        (pullback.fst _ h ≫ pullback.fst (W.obj i).hom π) (pullback.snd _ h ≫ e) _ :=
      pullback.lift_fst _ _ _
    have hd : d ≫ pullback.fst (pullback.snd (W.obj i).hom φ) e =
        (baseChangeCone W c hπ φ).π.app i := pullback.lift_fst _ _ _
    have ha : a ≫ pullback.fst (pullback.snd (W.obj i).hom π) h =
        pullback.fst (Scheme.Etale.mk (𝟙 c.pt)).hom h ≫ σ.left :=
      smallEtaleBaseChange_map_left_fst h σ
    have ha' : a ≫ pullback.snd (pullback.snd (W.obj i).hom π) h =
        pullback.snd (Scheme.Etale.mk (𝟙 c.pt)).hom h :=
      MorphismProperty.Over.w ((smallEtaleBaseChange h).map σ)
    have hσ : σ.left ≫ pullback.fst (W.obj i).hom π = c.π.app i := pullback.lift_fst _ _ _
    have hcond : pullback.fst (Scheme.Etale.mk (𝟙 c.pt)).hom h ≫ 𝟙 c.pt =
        pullback.snd (Scheme.Etale.mk (𝟙 c.pt)).hom h ≫ h := pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hb).trans ?_)
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) hd)).symm
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ha).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hσ).trans ?_)
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (t ≫ ·)
        (baseChangeLeg_fst W c hπ φ i))).symm
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact congrArg (· ≫ c.π.app i) ((Category.comp_id _).symm.trans hcond)
    · refine (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e) ha').trans ?_)
      exact ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) (baseChangeLeg_snd W c hπ φ i))).symm
  have n1 := ConcreteCategory.congr_hom
    (((smallEtaleSetBaseChange.{u, 0} e h φ π pullback.condition).app F).hom.naturality σ.op)
    (((smallEtaleInverseImageAdjunction.{u, 0} π).unit.app G).hom.app (op (W.obj i)) x)
  have n2 := smallEtaleSetBaseChange_unit_apply.{u, 0} e h φ π pullback.condition F (W.obj i) x
  have hm := ConcreteCategory.congr_hom (congrArg (fun m => P.obj.map (Quiver.Hom.op m)) hM)
    (((smallEtaleInverseImageAdjunction.{u, 0} e).unit.app F).hom.app
      (op ((smallEtaleBaseChange φ).obj (W.obj i))) x)
  simp only [op_comp, Functor.map_comp] at n1 hm
  exact n1.trans ((congrArg (P.obj.map ((smallEtaleBaseChange h).map σ).op) n2).trans hm)

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- The restriction map of the inverse image of `F` to `A ×_S T` along `unitBaseChangeToUnit` is
bijective. -/
theorem bijective_unitBaseChangeToUnit_map (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (((smallEtaleInverseImage.{u, 0} (pullback.fst φ π)).obj F).obj.map
      (unitBaseChangeToUnit W c (π := π) φ).op) := by
  let inv : Scheme.Etale.mk (𝟙 (pullback φ π)) ⟶
      (smallEtaleBaseChange (pullback.snd φ π)).obj (Scheme.Etale.mk (𝟙 c.pt)) :=
    MorphismProperty.Over.homMk (pullback.lift (pullback.snd φ π) (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) trivial
  have h1 : unitBaseChangeToUnit W c (π := π) φ ≫ inv = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.snd _ (pullback.snd φ π) ≫ pullback.lift (pullback.snd φ π) (𝟙 _) _ = 𝟙 _
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
      have hc : pullback.fst (Scheme.Etale.mk (𝟙 c.pt)).hom (pullback.snd φ π) ≫ 𝟙 c.pt =
          pullback.snd (Scheme.Etale.mk (𝟙 c.pt)).hom (pullback.snd φ π) ≫ pullback.snd φ π :=
        pullback.condition
      exact ((Category.comp_id _).symm.trans hc).symm.trans (Category.id_comp _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  have h2 : inv ≫ unitBaseChangeToUnit W c (π := π) φ = 𝟙 _ :=
    MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)
  have : IsIso (((smallEtaleInverseImage.{u, 0} (pullback.fst φ π)).obj F).obj.map
      (unitBaseChangeToUnit W c (π := π) φ).op) :=
    ⟨⟨((smallEtaleInverseImage.{u, 0} (pullback.fst φ π)).obj F).obj.map inv.op, by
      rw [← Functor.map_comp, ← op_comp, h2, op_id, CategoryTheory.Functor.map_id], by
      rw [← Functor.map_comp, ← op_comp, h1, op_id, CategoryTheory.Functor.map_id]⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

/-- **Stacks 03Q9 in degree zero for sheaves of sets, at the limit of the neighbourhoods.** If the
`W_i` are affine and `φ` is quasi-compact and quasi-separated, the base change map is bijective on
global sections over `T`. -/
theorem bijective_smallEtaleSetBaseChange_app_unit [∀ i, IsAffine (W.obj i).left] (hc : IsLimit c)
    (hπ : ∀ i, c.π.app i ≫ (W.obj i).hom = π)
    [QuasiCompact φ] [QuasiSeparated φ] (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ π) (pullback.snd φ π) φ π
        pullback.condition).app F).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))) := by
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (W.map a).left := fun {i j} a =>
    @isAffineHom_of_isAffine _ _ (W.map a).left (inferInstanceAs (IsAffine (W.obj i).left))
      (inferInstanceAs (IsAffine (W.obj j).left))
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((baseChangeSystem W φ).map a).left := fun a =>
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_smallEtaleBaseChange_map_left φ (W.map a)) inferInstance
  have hA : IsAffine (W.obj (op ⊥)).left := inferInstance
  have hcpt : CompactSpace (W.obj (op ⊥)).left := inferInstance
  have hqs : QuasiSeparatedSpace (W.obj (op ⊥)).left := inferInstance
  have : CompactSpace ((baseChangeSystem W φ).obj (op ⊥)).left := by
    change CompactSpace ↥(Limits.pullback (W.obj (op ⊥)).hom φ)
    exact @AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact_1
      _ _ _ (W.obj (op ⊥)).hom φ _ hcpt
  have : QuasiSeparatedSpace ((baseChangeSystem W φ).obj (op ⊥)).left := by
    change QuasiSeparatedSpace ↥(Limits.pullback (W.obj (op ⊥)).hom φ)
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (W.obj (op ⊥)).hom φ) hqs _
  let G := ((smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
    S.smallEtaleTopology A.smallEtaleTopology).obj F
  obtain ⟨hls, hli⟩ := limitSections_colimit W c hc hπ G
  obtain ⟨hμs, hμi⟩ := limitSections_colimit (baseChangeSystem W φ) (baseChangeCone W c hπ φ)
    (baseChangeConeIsLimit W c hπ φ hc) (baseChangeCone_π_comp_hom W c hπ φ) F
  have hρ := bijective_unitBaseChangeToUnit_map W c (π := π) φ F
  have key := smallEtaleSetBaseChange_limitSections W c hπ φ F
  have htr := fun {i j : I} (d : i ≤ j) (x : F.obj.obj (op ((smallEtaleBaseChange φ).obj
      (W.obj (op i))))) => ConcreteCategory.congr_hom (limitSections_transition W c hπ G d) x
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨i, x, rfl⟩ := hls a
    obtain ⟨j, y, rfl⟩ := hls b
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    rw [← htr hik x, ← htr hjk y] at hab ⊢
    simp only [ConcreteCategory.comp_apply] at hab ⊢
    have hab' := (key (op k) _).symm.trans (hab.trans (key (op k) _))
    obtain ⟨l, hkl, hl⟩ := hμi k _ _ (hρ.1 hab')
    exact (htr hkl _).symm.trans ((congrArg (limitSections W c hπ G (op l)) hl).trans (htr hkl _))
  · obtain ⟨t', rfl⟩ := hρ.2 t
    obtain ⟨i, x, rfl⟩ := hμs t'
    exact ⟨_, key (op i) x⟩

/-- **Stacks 03Q9 in degree zero for sheaves of sets, at the limit of the neighbourhoods**, on
global sections. -/
theorem isIso_Γ_map_smallEtaleSetBaseChange [∀ i, IsAffine (W.obj i).left] (hc : IsLimit c)
    (hπ : ∀ i, c.π.app i ≫ (W.obj i).hom = π)
    [QuasiCompact φ] [QuasiSeparated φ] (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    IsIso ((Sheaf.Γ c.pt.smallEtaleTopology (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ π) (pullback.snd φ π) φ π
        pullback.condition).app F)) := by
  rw [NatIso.isIso_map_iff (Sheaf.ΓNatIsoSheafSections _ (Type (u + 1)) (isTerminalEtaleMkId c.pt))]
  exact (isIso_iff_bijective _).2 (bijective_smallEtaleSetBaseChange_app_unit W c φ hc hπ F)

/-- `isIso_Γ_map_smallEtaleSetBaseChange` with the apex of the cone replaced by a scheme equal to
it. -/
theorem isIso_Γ_map_smallEtaleSetBaseChange_of_eq [∀ i, IsAffine (W.obj i).left] (hc : IsLimit c)
    {T : Scheme.{u}} (hT : c.pt = T) {π' : T ⟶ S}
    (hπ' : ∀ i, c.π.app i ≫ (W.obj i).hom = eqToHom hT ≫ π')
    [QuasiCompact φ] [QuasiSeparated φ] (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    IsIso ((Sheaf.Γ T.smallEtaleTopology (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ π') (pullback.snd φ π') φ π'
        pullback.condition).app F)) := by
  subst hT
  exact isIso_Γ_map_smallEtaleSetBaseChange W c φ hc
    (fun i => (hπ' i).trans (Category.id_comp _)) F

end Stacks.EtaleCohomology.EtaleLimitSections
