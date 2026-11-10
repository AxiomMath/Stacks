module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseACoherence
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RanUnderlying
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunctionUnderlying

/-!
# The Beck–Chevalley comparison of case (A) is invertible

The Beck–Chevalley comparison `h^*(M|_Q) ⟶ (f_φ^* M)|_{u_φ Q}` of case (A) is the mate of the
strict identity of direct images; its mate along the localization adjunctions is a comparison of
direct images which, on sheaves of sets, is the conjugate of Stacks 03CF (b), and so is
invertible. Since iterated mates are conjugates, the Beck–Chevalley comparison is invertible.

## Main results

* `CategoryTheory.SliceTopos.isIso_overPushforwardMate`.
* `CategoryTheory.SimplicialSite.CartesianSlice.isIso_beckChevalleyA`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SliceTopos

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)
  [u.IsContinuous J K]

/-- **The direct-image Beck–Chevalley comparison of Stacks 03CF.** The mate, along the two
localization adjunctions `j⁻¹ ⊣ j_*`, of the strict identity `f'_* j_U⁻¹ = j_V⁻¹ f_*` of clause
(d): a comparison `f_* j_{U,*} ⟶ j_{V,*} f'_*`. -/
def overPushforwardMate :
    TwoSquare ((Over.forget (u.obj V)).sheafPushforwardCocontinuous (Type u)
        (K.over (u.obj V)) K)
      ((Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V) (K.over (u.obj V)))
      (u.sheafPushforwardContinuous (Type u) J K)
      ((Over.forget V).sheafPushforwardCocontinuous (Type u) (J.over V) J) :=
  mateEquiv ((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V)) K)
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
    (eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm)

/-- The direct-image comparison is invertible: it is the conjugate of clause (b). -/
theorem isIso_overPushforwardMate (hu : u.IsMorphismOfSites J K) :
    IsIso (overPushforwardMate J K u V) := by
  have := isIso_overPullbackCompSheafPullbackOverPostMate J K u V hu
  have h := iterated_mateEquiv_conjugateEquiv (u.sheafAdjunctionContinuous (Type u) J K)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V) (K.over (u.obj V)))
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
    ((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V)) K)
    (overPullbackCompSheafPullbackOverPostMate J K u V)
  have e : overPushforwardMate J K u V =
      mateEquiv ((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V)) K)
        ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
        (mateEquiv (u.sheafAdjunctionContinuous (Type u) J K)
          ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
            (K.over (u.obj V))) (overPullbackCompSheafPullbackOverPostMate J K u V)) :=
    congrArg (mateEquiv
        ((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V)) K)
        ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J))
      ((mateEquiv (u.sheafAdjunctionContinuous (Type u) J K)
          ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
            (K.over (u.obj V)))).apply_symm_apply
        (eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm)).symm
  rw [show (overPushforwardMate J K u V) = _ from e.trans h]
  infer_instance


section Presheaf

variable {H : Type*} [Category H]
  [∀ F : (Over V)ᵒᵖ ⥤ H, (Over.forget V).op.HasRightKanExtension F]
  [∀ F : (Over (u.obj V))ᵒᵖ ⥤ H, (Over.forget (u.obj V)).op.HasRightKanExtension F]

/-- The presheaf form of the direct-image comparison: the adjunct, along the right Kan extension
adjunction at `V`, of the counit of the one at `u V` restricted along `Over.post u`. -/
def overPushforwardMatePresheaf (N : (Over (u.obj V))ᵒᵖ ⥤ H) :
    u.op ⋙ (Over.forget (u.obj V)).op.ran.obj N ⟶
      (Over.forget V).op.ran.obj ((Over.post (X := V) u).op ⋙ N) :=
  ((Over.forget V).op.ranAdjunction H).homEquiv _ _
    (Functor.whiskerLeft (Over.post (X := V) u).op
      ((Over.forget (u.obj V)).op.ranCounit.app N))

/-- **The legs of the direct-image comparison.** At the index `(W, ψ)` of the limit computing the
right Kan extension at `V`, it is the leg at the index `(u W, u ψ)` of the one at `u V`. -/
theorem overPushforwardMatePresheaf_app_comp_ranπ (N : (Over (u.obj V))ᵒᵖ ⥤ H) (b : Cᵒᵖ)
    (j : StructuredArrow b (Over.forget V).op) :
    (overPushforwardMatePresheaf u V N).app b ≫
        Stacks.SheafOfModules.ranπ (Over.forget V).op ((Over.post (X := V) u).op ⋙ N) b j =
      Stacks.SheafOfModules.ranπ (Over.forget (u.obj V)).op N (u.op.obj b)
        (StructuredArrow.mk (Y := (Over.post (X := V) u).op.obj j.right) (u.op.map j.hom)) :=
  Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ (Over.forget V).op _ b j

end Presheaf

/-- The sheaf-level direct-image comparison has the presheaf-level one underneath. -/
theorem overPushforwardMate_app_hom (N : Sheaf (K.over (u.obj V)) (Type u)) :
    ((overPushforwardMate J K u V).app N).hom =
      overPushforwardMatePresheaf u V N.obj := by
  have h1 := mateEquiv_counit
    ((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V)) K)
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
    (eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm) N
  have h2 : (overPushforwardMate J K u V).app N =
      ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J).homEquiv _ _
        (((Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V)
          (K.over (u.obj V))).map
          (((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V))
            K).counit.app N)) := by
    refine (((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J).homEquiv _ _
      ).symm.injective ?_
    exact ((Adjunction.homEquiv_counit _ _ _ _).trans (h1.trans (Category.id_comp _))).trans
      (Equiv.symm_apply_apply _ _).symm
  have h3 : (((Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V)
        (K.over (u.obj V))).map
        (((Over.forget (u.obj V)).sheafAdjunctionCocontinuous (Type u) (K.over (u.obj V))
          K).counit.app N)).hom =
      Functor.whiskerLeft (Over.post (X := V) u).op
        ((Over.forget (u.obj V)).op.ranCounit.app N.obj) :=
    congrArg (Functor.whiskerLeft (Over.post (X := V) u).op)
      ((Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ N).trans
        (congrArg (fun t => NatTrans.app t N.obj)
          (Functor.ranAdjunction_counit (Over.forget (u.obj V)).op (Type u))))
  refine (congrArg (fun f => f.hom) h2).trans
    ((Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom _ _ _ _ _).trans ?_)
  exact congrArg _ h3

end CategoryTheory.SliceTopos

namespace CategoryTheory.SimplicialSite.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) (Q : (situation C).component n)

/-- Restriction of modules on a component to a slice, as the left adjoint of the direct image
along `Over.forget`. -/
abbrev overRestrictionAdj (k : SimplexCategory) (X : (situation C).component k) :=
  Stacks.SheafOfModules.RestrictRan.sheafAdjunction (Over.forget X)
    (((situation C).componentTopology k).over X) ((situation C).componentTopology k)
    ((situation C).componentRingSheaf O k)

/-- **The direct-image Beck–Chevalley comparison on sheaves of modules.** -/
def overPushforwardMateA :
    TwoSquare (Stacks.SheafOfModules.pushforwardCocontinuous.{u}
        (Over.forget ((transitionFunctorA C φ).obj Q))
        (Stacks.SheafOfModules.RestrictRan.sheafUnit (Over.forget ((transitionFunctorA C φ).obj Q))
          (((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q))
          ((situation C).componentTopology m) ((situation C).componentRingSheaf O m)))
      (slicePushforward C O φ Q) (SheafOfModules.pushforward.{u} (ringTransitionA C O φ))
      (Stacks.SheafOfModules.pushforwardCocontinuous.{u} (Over.forget Q)
        (Stacks.SheafOfModules.RestrictRan.sheafUnit (Over.forget Q)
          (((situation C).componentTopology n).over Q) ((situation C).componentTopology n)
          ((situation C).componentRingSheaf O n))) :=
  mateEquiv (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q))
    (overRestrictionAdj C O n Q) (TwoSquare.mk _ _ _ _ (overPushforwardIso C O φ Q).hom)


/-- The module-level direct-image comparison at one module is the transpose of the restricted
counit. -/
theorem overPushforwardMateA_app (N : SheafOfModules.{u}
    (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q))) :
    (overPushforwardMateA C O φ Q).app N =
      (overRestrictionAdj C O n Q).homEquiv _ _
        ((slicePushforward C O φ Q).map
          ((overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q)).counit.app N)) := by
  have h1 := mateEquiv_counit (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q))
    (overRestrictionAdj C O n Q) (TwoSquare.mk _ _ _ _ (overPushforwardIso C O φ Q).hom) N
  refine ((overRestrictionAdj C O n Q).homEquiv _ _).symm.injective ?_
  exact ((Adjunction.homEquiv_counit _ _ _ _).trans (h1.trans (Category.id_comp _))).trans
    (Equiv.symm_apply_apply _ _).symm


/-- The module-level direct-image comparison has the presheaf-level one underneath. -/
theorem toPresheaf_map_overPushforwardMateA_app (N : SheafOfModules.{u}
    (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q))) :
    (PresheafOfModules.toPresheaf _).map ((overPushforwardMateA C O φ Q).app N).val =
      SliceTopos.overPushforwardMatePresheaf (H := AddCommGrpCat.{u}) (transitionFunctorA C φ) Q
        N.val.presheaf := by
  have hc : (PresheafOfModules.toPresheaf _).map
      ((overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q)).counit.app N).val =
      (Over.forget ((transitionFunctorA C φ).obj Q)).op.ranCounit.app N.val.presheaf :=
    (congrArg (PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.RestrictRan.sheafAdjunction_counit_app_val _ _ _ _ N)).trans
      ((Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_counit_app _ _ N.val).trans
        (congrArg (fun t => NatTrans.app t N.val.presheaf)
          (Functor.ranAdjunction_counit _ _)))
  refine (congrArg (fun f => (PresheafOfModules.toPresheaf _).map f.val)
    (overPushforwardMateA_app C O φ Q N)).trans ?_
  refine (congrArg (PresheafOfModules.toPresheaf _).map
    (Stacks.SheafOfModules.RestrictRan.sheafAdjunction_homEquiv_val _ _ _ _ _)).trans ?_
  refine (Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_homEquiv _ _ _ _ _).trans ?_
  exact congrArg _
    (congrArg (Functor.whiskerLeft (Over.post (X := Q) (transitionFunctorA C φ)).op) hc)


/-- The abelian and the set-level direct-image comparisons agree under forgetting. -/
theorem forget_map_overPushforwardMatePresheaf_app
    (A : (Over ((transitionFunctorA C φ).obj Q))ᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ((situation C).component n)ᵒᵖ) :
    (forget AddCommGrpCat.{u}).map
        ((SliceTopos.overPushforwardMatePresheaf (H := AddCommGrpCat.{u})
          (transitionFunctorA C φ) Q A).app b) ≫
      ((forget AddCommGrpCat.{u}).rightKanExtensionCompIsoOfPreserves
        ((Over.post (X := Q) (transitionFunctorA C φ)).op ⋙ A) (Over.forget Q).op).hom.app b =
      ((forget AddCommGrpCat.{u}).rightKanExtensionCompIsoOfPreserves A
        (Over.forget ((transitionFunctorA C φ).obj Q)).op).hom.app
          ((transitionFunctorA C φ).op.obj b) ≫
        (SliceTopos.overPushforwardMatePresheaf (H := Type u) (transitionFunctorA C φ) Q
          (A ⋙ forget AddCommGrpCat.{u})).app b := by
  refine Stacks.SheafOfModules.ran_hom_ext (Over.forget Q).op
    ((Over.post (X := Q) (transitionFunctorA C φ)).op ⋙ A ⋙ forget AddCommGrpCat.{u})
    (fun j => ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g => (forget AddCommGrpCat.{u}).map
    ((SliceTopos.overPushforwardMatePresheaf (H := AddCommGrpCat.{u})
          (transitionFunctorA C φ) Q A).app b) ≫ g)
    (Stacks.SheafOfModules.ranCompIso_hom_app_comp_ranπ (Over.forget Q).op
      (forget AddCommGrpCat.{u}) ((Over.post (X := Q) (transitionFunctorA C φ)).op ⋙ A) b
        j)).trans ?_
  refine ((forget AddCommGrpCat.{u}).map_comp _ _).symm.trans ?_
  refine (congrArg (forget AddCommGrpCat.{u}).map
    (SliceTopos.overPushforwardMatePresheaf_app_comp_ranπ (transitionFunctorA C φ) Q A b
      j)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun g =>
      ((forget AddCommGrpCat.{u}).rightKanExtensionCompIsoOfPreserves A
        (Over.forget ((transitionFunctorA C φ).obj Q)).op).hom.app
          ((transitionFunctorA C φ).op.obj b) ≫ g)
    (SliceTopos.overPushforwardMatePresheaf_app_comp_ranπ (transitionFunctorA C φ) Q
      (A ⋙ forget AddCommGrpCat.{u}) b j)).symm
  exact (Stacks.SheafOfModules.ranCompIso_hom_app_comp_ranπ _ (forget AddCommGrpCat.{u}) A _ _).symm


/-- **The module-level direct-image comparison is invertible.** -/
theorem isIso_overPushforwardMateA : IsIso (overPushforwardMateA C O φ Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro b
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{u})]
  let N' : Sheaf (((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q))
      (Type u) := (sheafCompose _ (forget AddCommGrpCat.{u})).obj ((SheafOfModules.toSheaf _).obj N)
  have := SliceTopos.isIso_overPushforwardMate ((situation C).componentTopology n)
    ((situation C).componentTopology m) (transitionFunctorA C φ) Q (C.isMorphismOfSites φ)
  have h1 : IsIso ((SliceTopos.overPushforwardMate ((situation C).componentTopology n)
      ((situation C).componentTopology m) (transitionFunctorA C φ) Q).app N').hom :=
    Functor.map_isIso (sheafToPresheaf ((situation C).componentTopology n) (Type u))
      ((SliceTopos.overPushforwardMate ((situation C).componentTopology n)
        ((situation C).componentTopology m) (transitionFunctorA C φ) Q).app N')
  rw [SliceTopos.overPushforwardMate_app_hom] at h1
  have h2 : IsIso ((SliceTopos.overPushforwardMatePresheaf (H := Type u)
      (transitionFunctorA C φ) Q (N.val.presheaf ⋙ forget AddCommGrpCat.{u})).app b) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ h1 b
  have e := forget_map_overPushforwardMatePresheaf_app C φ Q N.val.presheaf b
  have e' : (forget AddCommGrpCat.{u}).map
      ((SliceTopos.overPushforwardMatePresheaf (H := AddCommGrpCat.{u})
        (transitionFunctorA C φ) Q N.val.presheaf).app b) = _ :=
    (Iso.eq_comp_inv (((forget AddCommGrpCat.{u}).rightKanExtensionCompIsoOfPreserves
      ((Over.post (X := Q) (transitionFunctorA C φ)).op ⋙ N.val.presheaf)
      (Over.forget Q).op).app b)).2 e
  have e'' := congrArg (fun f => (forget AddCommGrpCat.{u}).map (NatTrans.app f b))
    (toPresheaf_map_overPushforwardMateA_app C O φ Q N)
  refine (e''.trans e').symm ▸ ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (Iso.isIso_hom (((forget AddCommGrpCat.{u}).rightKanExtensionCompIsoOfPreserves
        N.val.presheaf (Over.forget ((transitionFunctorA C φ).obj Q)).op).app
          ((transitionFunctorA C φ).op.obj b))) h2)
    (Iso.isIso_inv _)

/-- **The Beck–Chevalley comparison of case (A) is invertible.** -/
theorem isIso_beckChevalleyA : IsIso (beckChevalleyA C O φ Q) := by
  have h := iterated_mateEquiv_conjugateEquiv
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ))
    (slicePullbackAdj C O φ Q) (overRestrictionAdj C O n Q)
    (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q)) (beckChevalleyA C O φ Q)
  have e : overPushforwardMateA C O φ Q =
      mateEquiv (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q))
        (overRestrictionAdj C O n Q)
        (mateEquiv (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ))
          (slicePullbackAdj C O φ Q) (beckChevalleyA C O φ Q)) :=
    congrArg (mateEquiv (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q))
        (overRestrictionAdj C O n Q))
      ((mateEquiv (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ))
          (slicePullbackAdj C O φ Q)).apply_symm_apply
        (TwoSquare.mk _ _ _ _ (overPushforwardIso C O φ Q).hom)).symm
  have := isIso_overPushforwardMateA C O φ Q
  have : IsIso (conjugateEquiv
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).comp
        (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q)))
      ((overRestrictionAdj C O n Q).comp (slicePullbackAdj C O φ Q))
      (beckChevalleyA C O φ Q)) := by
    rw [← h, ← e]
    infer_instance
  exact conjugateEquiv_of_iso
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).comp
      (overRestrictionAdj C O m ((transitionFunctorA C φ).obj Q)))
    ((overRestrictionAdj C O n Q).comp (slicePullbackAdj C O φ Q))
    (beckChevalleyA C O φ Q)

end CategoryTheory.SimplicialSite.CartesianSlice
