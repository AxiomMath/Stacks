module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverCech
public import StacksFrontier.CategoryTheory.Sites.FlatObjectsSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# The flat affine schemes over an affine object of the big fppf site of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `U`
an object of `(Spaces/X)_fppf` identified with the algebraic space of an affine scheme `V₀`. The
affine schemes over `U` whose ring is flat over the ring of `U` form a subsite, with the coverings
by finite families of flat morphisms which are fppf coverings. Base change of modules over the
ring of `U` is exact on it, so the homology of a short complex of sheaves of modules whose
base-change comparisons are invertible on it again has invertible base-change comparison.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.ringFunctor`: the ring of an affine
  scheme over `U`, as a presheaf of commutative rings.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.FlatOver`: the affine schemes over `U`
  flat over `V₀`.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.flatTopology`: their topology.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.flat_ringFunctor_of_isPullback`: flat
  ring maps are stable under base change along fibre products of affine schemes over `U`.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.flat_ringFunctor_map_of_flat`: the ring
  map of a flat morphism of affine schemes is flat.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.isIso_flatComparison_app_homology`: the
  base-change comparison on the flat affine schemes is invertible at the homology of a short
  complex as soon as it is invertible at its three terms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace CategoryTheory

variable {𝒜 ℬ ℳ : Type*} [Category* 𝒜] [Category* ℬ] [Category* ℳ] [Abelian 𝒜] [Abelian ℬ]
  [Abelian ℳ]

/-- **A natural transformation `E ⋙ L ⟶ 𝟭` which is invertible on the essential image of an exact
functor `L` is invertible on the image under an exact functor `Φ` of the homology of a short
complex, as soon as it is invertible on the images of its three terms.** -/
theorem isIso_app_map_homology (Φ : 𝒜 ⥤ ℬ) [Φ.PreservesZeroMorphisms] [Φ.PreservesHomology]
    (L : ℳ ⥤ ℬ) [L.PreservesZeroMorphisms] [L.PreservesHomology] (E : ℬ ⥤ ℳ)
    [E.PreservesZeroMorphisms] (κ : E ⋙ L ⟶ 𝟭 ℬ)
    (hκ : ∀ M, IsIso (κ.app (L.obj M))) (S : ShortComplex 𝒜)
    (h₁ : IsIso (κ.app (Φ.obj S.X₁))) (h₂ : IsIso (κ.app (Φ.obj S.X₂)))
    (h₃ : IsIso (κ.app (Φ.obj S.X₃))) :
    IsIso (κ.app (Φ.obj S.homology)) := by
  let S' := S.map Φ
  let φ : S'.map (E ⋙ L) ⟶ S' :=
    { τ₁ := κ.app _, τ₂ := κ.app _, τ₃ := κ.app _
      comm₁₂ := (κ.naturality S'.f).symm, comm₂₃ := (κ.naturality S'.g).symm }
  have : IsIso φ.τ₁ := h₁
  have : IsIso φ.τ₂ := h₂
  have : IsIso φ.τ₃ := h₃
  have : IsIso φ := ShortComplex.isIso_of_isIso φ
  let e : Φ.obj S.homology ≅ L.obj (S'.map E).homology :=
    (S.mapHomologyIso Φ).symm ≪≫ (asIso (ShortComplex.homologyMap φ)).symm ≪≫
      (S'.map E).mapHomologyIso L
  exact (NatTrans.isIso_app_iff_of_iso κ e).2 (hκ _)

end CategoryTheory

namespace Stacks.PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsContinuous J K] (R : Sheaf K RingCat.{u})
  [Stacks.TerminalBaseChange.CommSections R.obj]
  [Stacks.TerminalBaseChange.CommSections
    ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj]

/-- **The base-change comparison of the restriction of a sheaf of modules along a continuous
functor is the base-change comparison of the sheaf itself** along the image morphism. -/
theorem isIso_restrictionBaseChange_pushforward_iff (M : SheafOfModules.{u} R) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{_, _, u, u} (R := Stacks.TerminalBaseChange.commPresheaf
        ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)
      ((SheafOfModules.pushforward.{u}
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R))).obj M).val f) ↔
    IsIso (restrictionBaseChange.{_, _, u, u} (R := Stacks.TerminalBaseChange.commPresheaf R.obj)
      M.val (G.op.map f)) := Iff.rfl

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces} {U : BigFppfSpaceOver T X}

variable (T U) in
/-- The ring of an affine scheme over `U`, as a presheaf of commutative rings. -/
noncomputable abbrev ringFunctor : (AffineSchemesOver T U)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Stacks.TerminalBaseChange.commPresheaf (ringPresheaf (T := T) (V := U))

variable (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)

include hV₀ e in
/-- **Flat ring maps are stable under base change along fibre products of affine schemes over
`U`.** -/
theorem flat_ringFunctor_of_isPullback {P Y₁ Y₂ Y₀ : AffineSchemesOver T U} {fst : P ⟶ Y₁}
    {snd : P ⟶ Y₂} {f : Y₁ ⟶ Y₀} {g : Y₂ ⟶ Y₀} (h : IsPullback fst snd f g)
    (hg : ((ringFunctor T U).map g.op).hom.Flat) : ((ringFunctor T U).map fst.op).hom.Flat := by
  have hpo := isPushout_ringPresheaf (f := f) (g := g) (p₁ := fst) (p₂ := snd)
    (h.map (toSchemeFunctor V₀ e))
  have h₁ := RingHom.Flat.isStableUnderBaseChange.pushout_inl RingHom.Flat.respectsIso
    ((ringFunctor T U).map f.op) ((ringFunctor T U).map g.op) hg
  have h₂ : pushout.inl ((ringFunctor T U).map f.op) ((ringFunctor T U).map g.op) ≫
      hpo.isoPushout.inv = (ringFunctor T U).map fst.op := hpo.inl_isoPushout_inv
  rw [← h₂]
  exact (RingHom.Flat.respectsIso.cancel_right_isIso (g := hpo.isoPushout.inv) _).2 h₁

/-- **The ring map of a flat morphism of affine schemes over `U` is flat.** -/
theorem flat_ringFunctor_map_of_flat {A A' : AffineSchemesOver T U} (f : A ⟶ A')
    (hf : Flat ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f.hom.left)) :
    ((ringFunctor T U).map f.op).hom.Flat := by
  have : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.obj.left) :=
    A.property
  have : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A'.obj.left) :=
    A'.property
  have h : (ringFunctor T U).map f.op ≫ (ringIso A).hom = (ringIso A').hom ≫ CommRingCat.ofHom
      ((Scheme.Γ.map ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map
        f.hom.left).op).hom.ulift) := ringIso_hom_naturality f
  have h₁ : ((ringFunctor T U).map f.op ≫ (ringIso A).hom).hom.Flat := by
    rw [h]
    exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).2
      (RingHom.Flat.ulift_iff.2 (Scheme.Hom.flat_appTop
        ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f.hom.left)))
  exact (RingHom.Flat.respectsIso.cancel_right_isIso _ (ringIso A).hom).1 h₁

/-! ### The subsite of flat affine schemes -/

/-- The affine schemes over `U` whose ring is flat over the ring of `V₀`. -/
abbrev FlatOver :=
  Stacks.FlatObjectsSubsite.FlatObjects (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e)

/-- The inclusion of the flat affine schemes over `U` into the affine schemes over `U`. -/
abbrev flatι : FlatOver V₀ hV₀ e ⥤ AffineSchemesOver T U :=
  (Stacks.FlatObjectsSubsite.IsFlatOver (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e)).ι

/-- The topology on the flat affine schemes over `U`: finite families of flat morphisms which
are fppf coverings. -/
noncomputable abbrev flatTopology : GrothendieckTopology (FlatOver V₀ hV₀ e) :=
  letI := hasFiniteLimits V₀ e hV₀
  Stacks.FlatObjectsSubsite.topology (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e) topology
    (fun h hg ↦ flat_ringFunctor_of_isPullback V₀ hV₀ e h hg)

/-- The inclusion of the flat affine schemes over `U` is continuous. -/
instance flatι_isContinuous : (flatι V₀ hV₀ e).IsContinuous (flatTopology V₀ hV₀ e) topology :=
  letI := hasFiniteLimits V₀ e hV₀
  Stacks.FlatObjectsSubsite.ι_isContinuous (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e) topology
    (fun h hg ↦ flat_ringFunctor_of_isPullback V₀ hV₀ e h hg)

/-- **Every covering sieve of a flat affine scheme over `U` contains a finite family of flat
morphisms from flat affine schemes which is an fppf covering.** -/
theorem exists_flat_ofArrows_le (Y : FlatOver V₀ hV₀ e) (R : Sieve Y.obj)
    (hR : R ∈ topology (T := T) (V := U) Y.obj) :
    ∃ (I : Type u) (Z : I → FlatOver V₀ hV₀ e) (φ : ∀ i, Z i ⟶ Y),
      (∀ i, ((ringFunctor T U).map (φ i).hom.op).hom.Flat) ∧
      Sieve.ofArrows (fun i ↦ (Z i).obj) (fun i ↦ (φ i).hom) ∈ topology (T := T) (V := U) Y.obj ∧
      ∀ i, R (φ i).hom := by
  obtain ⟨n, Z, hZ, φ, hRφ, hcov, hfppf⟩ := exists_finite_fppf_ofArrows_le Y.obj R hR
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf
  have hflat : ∀ i, ((ringFunctor T U).map (homOfScheme Y.obj (hZ i) (φ i)).op).hom.Flat :=
    fun i ↦ flat_ringFunctor_map_of_flat _ (hfppf.2 i).1
  refine ⟨ULift.{u} (Fin n), fun i ↦ ⟨memberObj Y.obj (hZ i.down) (φ i.down),
      Stacks.FlatObjectsSubsite.isFlatOver_of_flat _ (hflat i.down) Y.property⟩,
    fun i ↦ ObjectProperty.homMk (homOfScheme Y.obj (hZ i.down) (φ i.down)),
    fun i ↦ hflat i.down, ?_, fun i ↦ hRφ i.down⟩
  refine (topology (T := T) (V := U)).superset_covering ((Sieve.generate_le_iff _ _).2 ?_) hcov
  rintro _ _ ⟨i⟩
  exact Sieve.ofArrows_mk (I := ULift.{u} (Fin n)) _ _ ⟨i⟩

/-- The inclusion of the flat affine schemes over `U` is cocontinuous. -/
instance flatι_isCocontinuous :
    (flatι V₀ hV₀ e).IsCocontinuous (flatTopology V₀ hV₀ e) topology :=
  letI := hasFiniteLimits V₀ e hV₀
  Stacks.FlatObjectsSubsite.ι_isCocontinuous (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e) topology
    (fun h hg ↦ flat_ringFunctor_of_isPullback V₀ hV₀ e h hg) (exists_flat_ofArrows_le V₀ hV₀ e)

/-! ### Modules on the flat affine schemes -/

/-- The structure sheaf of rings on the flat affine schemes over `U`. -/
noncomputable abbrev flatRingSheaf : Sheaf (flatTopology V₀ hV₀ e) RingCat.{u + 1} :=
  ((flatι V₀ hV₀ e).sheafPushforwardContinuous RingCat.{u + 1} (flatTopology V₀ hV₀ e)
    topology).obj (Stacks.DenseSubsiteModules.ringRestriction (topology (T := T) (V := U))
      ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf)

/-- The sections of the structure sheaf of rings on the flat affine schemes over `U` are
commutative. -/
instance flatRingSheaf_commSections :
    Stacks.TerminalBaseChange.CommSections (flatRingSheaf V₀ hV₀ e).obj where
  mul_comm A a b := Stacks.TerminalBaseChange.CommSections.mul_comm
    (O := ringPresheaf (T := T) (V := U)) (op A.unop.obj) a b

/-- **Restriction of sheaves of modules from `(Spaces/X)_fppf` to the flat affine schemes over
`U`.** -/
noncomputable abbrev flatRestriction :
    SheafOfModules.{u + 1} (bigFppfRingSheaf T X) ⥤
      SheafOfModules.{u + 1} (flatRingSheaf V₀ hV₀ e) :=
  SheafOfModules.overFunctor (bigFppfRingSheaf T X) U ⋙
    Stacks.DenseSubsiteModules.moduleRestriction (topology (T := T) (V := U))
      ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf ⋙
    SheafOfModules.pushforward.{u + 1} (𝟙 (flatRingSheaf V₀ hV₀ e))

/-- Restriction to the flat affine schemes over `U` preserves finite limits. -/
instance flatRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (flatRestriction V₀ hV₀ e) := by
  dsimp only [flatRestriction]
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
/-- Restriction to the flat affine schemes over `U` preserves finite colimits. -/
instance flatRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (flatRestriction V₀ hV₀ e) := by
  have h₁ : PreservesFiniteColimits (SheafOfModules.overFunctor.{u + 1} (bigFppfRingSheaf T X) U) :=
    open Stacks.SheafOfModules.PushforwardRightExact in
    preservesFiniteColimits_pushforward_of_isAlmostCocontinuous.{u + 1, u + 1, _, _, _, _}
      (Over.forget U) (𝟙 ((bigFppfRingSheaf T X).over U))
      (isAlmostCocontinuous_of_isCocontinuous _ _ _)
  have h₃ : PreservesFiniteColimits
      (SheafOfModules.pushforward.{u + 1} (𝟙 (flatRingSheaf V₀ hV₀ e))) :=
    open Stacks.SheafOfModules.PushforwardRightExact in
    preservesFiniteColimits_pushforward_of_isAlmostCocontinuous.{u + 1, u + 1, _, _, _, _}
      (flatι V₀ hV₀ e) (𝟙 (flatRingSheaf V₀ hV₀ e)) (isAlmostCocontinuous_of_isCocontinuous _ _ _)
  dsimp only [flatRestriction]
  infer_instance

/-- The terminal flat affine scheme over `U`. -/
noncomputable abbrev flatIsTerminal :
    IsTerminal (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U)
      (isTerminalOfIso V₀ hV₀ e)) :=
  Stacks.FlatObjectsSubsite.isTerminal (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e)

/-- The base change presheaf `A ↦ 𝒪(A) ⊗ M` on the flat affine schemes over `U`. -/
noncomputable abbrev flatBaseChangePresheaf :
    ModuleCat.{u + 1} ((flatRingSheaf V₀ hV₀ e).obj.obj
        (op (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e)))) ⥤
      PresheafOfModules.{u + 1} (flatRingSheaf V₀ hV₀ e).obj :=
  Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (flatRingSheaf V₀ hV₀ e).obj
    (flatIsTerminal V₀ hV₀ e)

/-- **The base change presheaf on the flat affine schemes over `U` is a sheaf.** -/
theorem isSheaf_flatBaseChangePresheaf (M : ModuleCat.{u + 1} ((flatRingSheaf V₀ hV₀ e).obj.obj
    (op (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e))))) :
    Presheaf.IsSheaf (flatTopology V₀ hV₀ e) ((flatBaseChangePresheaf V₀ hV₀ e).obj M).presheaf :=
  (flatι V₀ hV₀ e).op_comp_isSheaf_of_isSheaf (flatTopology V₀ hV₀ e) topology _
    (isSheaf_baseChangePresheaf (isTerminalOfIso V₀ hV₀ e) M)

/-- **The base change sheaf `A ↦ 𝒪(A) ⊗ M` on the flat affine schemes over `U`.** -/
noncomputable def flatBaseChange :
    ModuleCat.{u + 1} ((flatRingSheaf V₀ hV₀ e).obj.obj
        (op (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e)))) ⥤
      SheafOfModules.{u + 1} (flatRingSheaf V₀ hV₀ e) where
  obj M := ⟨(flatBaseChangePresheaf V₀ hV₀ e).obj M, isSheaf_flatBaseChangePresheaf V₀ hV₀ e M⟩
  map φ := ⟨(flatBaseChangePresheaf V₀ hV₀ e).map φ⟩
  map_id M := SheafOfModules.hom_ext ((flatBaseChangePresheaf V₀ hV₀ e).map_id M)
  map_comp φ ψ := SheafOfModules.hom_ext ((flatBaseChangePresheaf V₀ hV₀ e).map_comp φ ψ)

/-- The base change sheaf followed by the forgetful functor is the base change presheaf. -/
noncomputable def flatBaseChangeForgetIso :
    flatBaseChange V₀ hV₀ e ⋙ SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e) ≅
      flatBaseChangePresheaf V₀ hV₀ e :=
  Iso.refl _

/-- The base change sheaf functor is additive. -/
instance flatBaseChange_additive : (flatBaseChange V₀ hV₀ e).Additive where
  map_add {_ _ _ _} := SheafOfModules.hom_ext ((flatBaseChangePresheaf V₀ hV₀ e).map_add)

/-- The base change presheaf functor on the flat affine schemes over `U` preserves finite
limits. -/
instance flatBaseChangePresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (flatBaseChangePresheaf V₀ hV₀ e) := by
  refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦
    ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun Y ↦ ?_)⟩⟩⟩⟩
  have hflat : (Stacks.TerminalBaseChange.rho (flatRingSheaf V₀ hV₀ e).obj
      (flatIsTerminal V₀ hV₀ e) Y).Flat := Y.unop.property
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft K
      (Stacks.TerminalBaseChange.baseChangeEvaluationIso.{u + 1} (flatRingSheaf V₀ hV₀ e).obj
        (flatIsTerminal V₀ hV₀ e) Y)).symm _).symm
    (IsLimit.ofIsoLimit (isLimitOfPreserves (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (Stacks.TerminalBaseChange.rho (flatRingSheaf V₀ hV₀ e).obj (flatIsTerminal V₀ hV₀ e) Y)) hc)
      (Cone.ext (Iso.refl _) (fun _ ↦ rfl)))

/-- The base change sheaf functor preserves finite limits. -/
instance flatBaseChange_preservesFiniteLimits :
    PreservesFiniteLimits (flatBaseChange V₀ hV₀ e) := by
  have : PreservesFiniteLimits (flatBaseChange V₀ hV₀ e ⋙
      SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e)) :=
    inferInstanceAs (PreservesFiniteLimits (flatBaseChangePresheaf V₀ hV₀ e))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e))

/-- The base change sheaf functor preserves finite colimits. -/
instance flatBaseChange_preservesFiniteColimits :
    PreservesFiniteColimits (flatBaseChange V₀ hV₀ e) := by
  have : PreservesFiniteColimits (flatBaseChange V₀ hV₀ e ⋙
      SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e)) :=
    inferInstanceAs (PreservesFiniteColimits (flatBaseChangePresheaf V₀ hV₀ e))
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e))

/-- **The comparison of a sheaf of modules on the flat affine schemes with the base change of its
sections over `U`.** -/
noncomputable def flatComparison :
    SheafOfModules.evaluation.{u + 1} (flatRingSheaf V₀ hV₀ e)
        (op (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U) (isTerminalOfIso V₀ hV₀ e))) ⋙
      flatBaseChange V₀ hV₀ e ⟶ 𝟭 _ where
  app G := ⟨Stacks.TerminalBaseChange.baseChangeComparison.{u + 1} (flatRingSheaf V₀ hV₀ e).obj
    (flatIsTerminal V₀ hV₀ e) G.val⟩
  naturality _ _ f := SheafOfModules.hom_ext
    (Stacks.TerminalBaseChange.baseChangeComparison_naturality.{u + 1} _ _ f.val)

/-- The comparison on the flat affine schemes is invertible at `G` if and only if the base-change
comparison of its underlying presheaf of modules is. -/
lemma isIso_flatComparison_app_iff (G : SheafOfModules.{u + 1} (flatRingSheaf V₀ hV₀ e)) :
    IsIso ((flatComparison V₀ hV₀ e).app G) ↔
      IsIso (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1} (flatRingSheaf V₀ hV₀ e).obj
        (flatIsTerminal V₀ hV₀ e) G.val) :=
  ⟨fun _ ↦ inferInstanceAs
      (IsIso ((SheafOfModules.forget _).map ((flatComparison V₀ hV₀ e).app G))),
    fun h ↦ by
      have : IsIso ((SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e)).map
        ((flatComparison V₀ hV₀ e).app G)) := h
      exact isIso_of_reflects_iso _ (SheafOfModules.forget.{u + 1} (flatRingSheaf V₀ hV₀ e))⟩

/-- The comparison on the flat affine schemes is invertible at a base change sheaf. -/
instance isIso_flatComparison_app_flatBaseChange (M) :
    IsIso ((flatComparison V₀ hV₀ e).app ((flatBaseChange V₀ hV₀ e).obj M)) :=
  (isIso_flatComparison_app_iff V₀ hV₀ e _).2
    (Stacks.TerminalBaseChange.isIso_baseChangeComparison_baseChangePresheaf.{u + 1} _ _ M)

/-- The sheaf of modules on the affine schemes over `U` attached to a sheaf of modules on
`(Spaces/X)_fppf`. -/
noncomputable abbrev affineRestriction (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) :
    SheafOfModules.{u + 1} (Stacks.DenseSubsiteModules.ringRestriction (topology (T := T) (V := U))
      ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf) :=
  (Stacks.DenseSubsiteModules.moduleRestriction (topology (T := T) (V := U))
    ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf).obj (N.over U)

/-- The comparison on the flat affine schemes is invertible at the restriction of a sheaf of
modules which is cartesian over every flat affine scheme over `U`. -/
theorem isIso_flatComparison_app_flatRestriction (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (h : ∀ (Y : FlatOver V₀ hV₀ e) (g : Y.obj ⟶ ofIso V₀ hV₀ e),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := ringFunctor T U) (affineRestriction N).val g.op)) :
    IsIso ((flatComparison V₀ hV₀ e).app ((flatRestriction V₀ hV₀ e).obj N)) := by
  rw [isIso_flatComparison_app_iff]
  apply Stacks.TerminalBaseChange.isIso_baseChangeComparison_of_forall
  intro Y
  exact (Stacks.PresheafOfModules.isIso_restrictionBaseChange_pushforward_iff (flatι V₀ hV₀ e)
    (Stacks.DenseSubsiteModules.ringRestriction (topology (T := T) (V := U))
      ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf) (affineRestriction N)
    (Stacks.TerminalBaseChange.iota (flatIsTerminal V₀ hV₀ e) Y)).2 (h Y.unop _)

/-- Evaluation at the terminal flat affine scheme over `U` preserves zero morphisms. -/
instance : (SheafOfModules.evaluation.{u + 1} (flatRingSheaf V₀ hV₀ e)
    (op (Stacks.FlatObjectsSubsite.terminalObj (ringFunctor T U)
      (isTerminalOfIso V₀ hV₀ e)))).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **The homology of a short complex of sheaves of modules on `(Spaces/X)_fppf` which are
cartesian over the flat affine schemes over `U` is again cartesian there.** -/
theorem isIso_flatComparison_app_homology
    (S : ShortComplex (SheafOfModules.{u + 1} (bigFppfRingSheaf T X)))
    (h₁ : ∀ (Y : FlatOver V₀ hV₀ e) (g : Y.obj ⟶ ofIso V₀ hV₀ e),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := ringFunctor T U) (affineRestriction S.X₁).val g.op))
    (h₂ : ∀ (Y : FlatOver V₀ hV₀ e) (g : Y.obj ⟶ ofIso V₀ hV₀ e),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := ringFunctor T U) (affineRestriction S.X₂).val g.op))
    (h₃ : ∀ (Y : FlatOver V₀ hV₀ e) (g : Y.obj ⟶ ofIso V₀ hV₀ e),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := ringFunctor T U) (affineRestriction S.X₃).val g.op)) :
    IsIso ((flatComparison V₀ hV₀ e).app ((flatRestriction V₀ hV₀ e).obj S.homology)) :=
  isIso_app_map_homology (flatRestriction V₀ hV₀ e) (flatBaseChange V₀ hV₀ e) _
    (flatComparison V₀ hV₀ e) (fun _ ↦ inferInstance) S
    (isIso_flatComparison_app_flatRestriction V₀ hV₀ e _ h₁)
    (isIso_flatComparison_app_flatRestriction V₀ hV₀ e _ h₂)
    (isIso_flatComparison_app_flatRestriction V₀ hV₀ e _ h₃)

end AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver

end
