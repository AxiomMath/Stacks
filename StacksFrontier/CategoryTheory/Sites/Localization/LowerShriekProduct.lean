module

public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts

/-!
# `j_{U!} j_U^{-1} F = F × h_U^#`

Let `(C, J)` be a site, let `U` be an object of `C` and let `F` be a sheaf of sets on `C`.
Stacks 03EE asserts `j_{U!}j_U^{-1}F = F × h_U^#`.

As in `StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts`, `j_U^{-1}` is
Mathlib's `J.overPullback` and `j_{U!}` its
left adjoint `Functor.sheafPullback`. The source states the conclusion as an equality of sheaves,
identifying objects defined up to canonical isomorphism; the faithful rendering is a canonical
isomorphism in `Sh(C)`.

## Implementation

The source says this is "clear from the description of `j_{U!}` in Stacks 03CD", and that is
exactly
how it is obtained here. Since `j_U^{-1}F` is a sheaf, it is its own sheafification, so 03CD
applies and identifies `j_{U!}j_U^{-1}F` with the sheafification of the presheaf
`V ↦ ∐_{φ : V ⟶ U} (j_U^{-1}F)(V →φ U) = ∐_{φ : V ⟶ U} F(V)`. That presheaf is the product
`F × h_U` of presheaves (`prodIsLimit`), and sheafification preserves finite limits, so its
sheafification is `F^# × h_U^# = F × h_U^#`.

## Main results

* `CategoryTheory.OverShriek.prodIsLimit`: the coproduct presheaf attached to `j_U^{-1}F` is the
  product `F × h_U` of presheaves on `C`.
* `CategoryTheory.OverShriek.overShriekOverPullbackIso` and
  `CategoryTheory.OverShriek.overShriek_overPullback_iso`: Stacks 03EE.

Tags covered: 03EE.
-/

@[expose] public section

open CategoryTheory Opposite
universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] (U : C) (F : Cᵒᵖ ⥤ Type v)

/-! ### The coproduct presheaf attached to a restricted presheaf is a product

For a presheaf `F` on `C`, the presheaf `j_U^{-1}F` on `C/U` has `(j_U^{-1}F)(V →φ U) = F(V)`,
independently of `φ`, so the coproduct presheaf of Stacks 03CD becomes
`V ↦ Hom_C(V, U) × F(V)`, i.e. the product of `h_U` with `F`. -/

/-- The projection of `∐_{φ : V ⟶ U} F(V)` onto `F`, forgetting the index `φ`. -/
def prodFst : presheaf ((Over.forget U).op ⋙ F) ⟶ F where
  app _ := ↾fun p => p.2
  naturality _ _ _ := rfl

/-- The projection of `∐_{φ : V ⟶ U} F(V)` onto `h_U`, remembering only the index `φ`. -/
def prodSnd : presheaf ((Over.forget U).op ⋙ F) ⟶ yoneda.obj U where
  app _ := ↾fun p => p.1
  naturality _ _ _ := rfl

/-- The map into `∐_{φ : V ⟶ U} F(V)` determined by a map to `F` and a map to `h_U`. -/
def prodLift {T : Cᵒᵖ ⥤ Type v} (a : T ⟶ F) (b : T ⟶ yoneda.obj U) :
    T ⟶ presheaf ((Over.forget U).op ⋙ F)
    where
  app V := ↾fun x => ⟨b.app V x, a.app V x⟩
  naturality {V W} f := by
    ext x : 3
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · exact NatTrans.naturality_apply b f x
    · exact NatTrans.naturality_apply a f x

/-- **The coproduct presheaf attached to `j_U^{-1}F` is the product `F × h_U`.** -/
def prodIsLimit : Limits.IsLimit (Limits.BinaryFan.mk (prodFst U F) (prodSnd U F)) :=
  Limits.BinaryFan.isLimitMk (fun s => prodLift U F s.fst s.snd) (fun _ => rfl) (fun _ => rfl) <|
    by
    intro s m hfst hsnd
    ext V x
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · exact congrArg (fun t : s.pt.obj V ⟶ (yoneda.obj U).obj V => t x) (NatTrans.congr_app hsnd V)
    · exact congrArg (fun t : s.pt.obj V ⟶ F.obj V => t x) (NatTrans.congr_app hfst V)

noncomputable section

/-- The isomorphism `∐_{φ : V ⟶ U} F(V) ≅ F × h_U` of presheaves on `C`. -/
def prodIso : presheaf ((Over.forget U).op ⋙ F) ≅ F ⨯ yoneda.obj U :=
  (prodIsLimit U F).conePointUniqueUpToIso (Limits.limit.isLimit (Limits.pair F (yoneda.obj U)))

/-! ### Stacks 03EE -/

variable (J : GrothendieckTopology C)
variable [HasWeakSheafify (J.over U) (Type v)] [HasSheafify J (Type v)]
variable [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- **Stacks 03EE.** For a sheaf `F` on `C` and an object `U` of `C`,
`j_{U!}j_U^{-1}F ≅ F × h_U^#`. -/
def overShriekOverPullbackIso (F : Sheaf J (Type v)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).obj ((J.overPullback (Type v) U).obj F) ≅
      F ⨯ (presheafToSheaf J (Type v)).obj (yoneda.obj U) :=
  -- `j_U^{-1}F` is a sheaf, hence its own sheafification, so Stacks 03CD applies to it.
  ((Over.forget U).sheafPullback (Type v) (J.over U) J).mapIso
      (sheafificationIso ((J.overPullback (Type v) U).obj F)) ≪≫
    sheafifyIso ((Over.forget U).op ⋙ F.obj) J ≪≫
    -- The coproduct presheaf is the presheaf-level product `F × h_U` ...
    (presheafToSheaf J (Type v)).mapIso (prodIso U F.obj) ≪≫
    -- ... and sheafification preserves finite limits.
    Limits.PreservesLimitPair.iso (presheafToSheaf J (Type v)) F.obj (yoneda.obj U) ≪≫
    Limits.prod.mapIso (sheafificationIso F).symm (Iso.refl _)

/-- **Stacks 03EE**, packaged as the existence of the isomorphism
`j_{U!}j_U^{-1}F ≅ F × h_U^#`. -/
@[stacks 03EE]
theorem overShriek_overPullback_iso (F : Sheaf J (Type v)) :
    Nonempty
      (((Over.forget U).sheafPullback (Type v) (J.over U) J).obj
          ((J.overPullback (Type v) U).obj F) ≅
        F ⨯ (presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  ⟨overShriekOverPullbackIso U J F⟩

end

end CategoryTheory.OverShriek
