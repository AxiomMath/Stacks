module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification

/-!
# Pullback of modules along a continuous functor with a left adjoint

Let `F : C ⥤ D` be a functor with a left adjoint `L : D ⥤ C`, let `O₀` and `O` be presheaves of
commutative rings on `C` and `D`, and let `φ : O₀ ⟶ F.op ⋙ O`.  Then the inverse image of
presheaves along `F` is precomposition with `L`, with no colimit involved, and the pullback of
presheaves of modules along `φ` has the concrete description

`M ↦ (V ↦ O(V) ⊗_{O₀(L V)} M(L V))`,

the ring map `O₀(L V) ⟶ O(V)` being `φ` at `L V` followed by restriction along the unit
`V ⟶ F (L V)`; this is `Stacks.PullbackLeftAdjoint.transposeRingHom`, the adjoint transpose of
`φ`.  The description is restriction along `L`, left adjoint to restriction along `F` by
`Stacks.PresheafOfModules.pushforwardPushforwardAdj`, followed by objectwise extension of scalars
`Stacks.PullbackModel.extendScalars`, left adjoint to restriction of scalars.

For sheaves of modules the pullback is the sheafification of this presheaf, and so it is exact
as soon as the transposed ring maps are flat *locally*: if every object of `D` is covered by
objects `W` with `O₀(L W) ⟶ O(W)` flat, then the presheaf pullback of a monomorphism is locally
injective, its sheafification is a monomorphism, and a left adjoint between abelian categories
which preserves monomorphisms is exact.  This is the mechanism of Stacks 0GN1 and 0GNA, applied
to the pullback functor rather than to a single tensor product.

## Main definitions

* `Stacks.PullbackLeftAdjoint.transposeRingHom`: the ring maps `O₀(L V) ⟶ O(V)`.
* `Stacks.PullbackLeftAdjoint.pullbackModel`: the presheaf of modules `V ↦ O(V) ⊗ M(L V)`.
* `Stacks.PullbackLeftAdjoint.modelAdjunction`: it is left adjoint to the pushforward along `φ`.

## Main results

* `Stacks.PullbackLeftAdjoint.isRightAdjoint_pushforward`: the pushforward of presheaves of
  modules along `φ` is a right adjoint, with no smallness hypothesis.
* `Stacks.PullbackLeftAdjoint.preservesFiniteLimits_pullback`: **the pullback of sheaves of
  modules along `φ` is exact when the transposed ring maps are flat on a covering of every
  object.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂

namespace Stacks.PullbackLeftAdjoint

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ F)
  {O₀ : Cᵒᵖ ⥤ CommRingCat.{w}} {O : Dᵒᵖ ⥤ CommRingCat.{w}} (φ : O₀ ⟶ F.op ⋙ O)

/-- **The adjoint transpose of `φ`**: the ring maps `O₀(L V) ⟶ O(F (L V)) ⟶ O(V)`, the second
being restriction along the unit `V ⟶ F (L V)` of `L ⊣ F`. -/
def transposeRingHom : L.op ⋙ O₀ ⟶ O :=
  Functor.whiskerLeft L.op φ ≫ Functor.whiskerRight (NatTrans.op adj.unit) O

/-- The component of `transposeRingHom` at `V` is `φ` at `L V` followed by restriction along the
unit `V ⟶ F (L V)`. -/
theorem transposeRingHom_app (V : Dᵒᵖ) :
    (transposeRingHom adj φ).app V = φ.app (op (L.obj V.unop)) ≫ O.map (adj.unit.app V.unop).op :=
  rfl

/-- The ring maps `O₀(U) ⟶ O₀(L (F U))` given by restriction along the counit of `L ⊣ F`. -/
abbrev counitRingHom :
    O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ L.op ⋙ O₀ ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight (NatTrans.op adj.counit) (O₀ ⋙ forget₂ CommRingCat RingCat)

/-- Restriction of presheaves of modules along `L`: `M ↦ M ∘ L`. -/
abbrev restriction :
    _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat) ⥤
      _root_.PresheafOfModules.{w} (L.op ⋙ O₀ ⋙ forget₂ CommRingCat RingCat) :=
  _root_.PresheafOfModules.pushforward.{w} (F := L)
    (𝟙 (L.op ⋙ O₀ ⋙ forget₂ CommRingCat RingCat))

/-- Restriction along `L` is left adjoint to restriction along `F`. -/
def restrictionAdjunction :
    restriction (L := L) (O₀ := O₀) ⊣
      _root_.PresheafOfModules.pushforward.{w} (counitRingHom adj (O₀ := O₀)) :=
  Stacks.PresheafOfModules.pushforwardPushforwardAdj.{w} adj
    (𝟙 (L.op ⋙ O₀ ⋙ forget₂ CommRingCat RingCat)) (counitRingHom adj)
    (by rw [Functor.whiskerLeft_id', Category.comp_id])
    (by
      ext V : 2
      have h := congrArg Quiver.Hom.op (adj.left_triangle_components V.unop)
      simp only [op_comp] at h
      change (O₀ ⋙ forget₂ CommRingCat RingCat).map (adj.counit.app (L.obj V.unop)).op ≫
        (O₀ ⋙ forget₂ CommRingCat RingCat).map (L.map (adj.unit.app V.unop)).op = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, h]
      exact CategoryTheory.Functor.map_id _ _)

/-- **The pullback of presheaves of modules along `φ`, concretely**:
`M ↦ (V ↦ O(V) ⊗_{O₀(L V)} M(L V))`. -/
def pullbackModel :
    _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat) ⥤
      _root_.PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat) :=
  restriction ⋙ Stacks.PullbackModel.extendScalars (transposeRingHom adj φ)

/-- Restriction along the counit of `L ⊣ F` followed by the transpose of `φ`, read at `F U`, is
`φ`. -/
theorem whiskerRight_counit_comp_transposeRingHom :
    Functor.whiskerRight (NatTrans.op adj.counit) O₀ ≫
      Functor.whiskerLeft F.op (transposeRingHom adj φ) = φ := by
  ext U : 2
  have h := congrArg Quiver.Hom.op (adj.right_triangle_components U.unop)
  simp only [op_comp] at h
  have hφ : O₀.map (adj.counit.app U.unop).op ≫ φ.app (op (L.obj (F.obj U.unop))) =
      φ.app U ≫ O.map (F.map (adj.counit.app U.unop)).op :=
    φ.naturality (adj.counit.app U.unop).op
  change O₀.map (adj.counit.app U.unop).op ≫ φ.app (op (L.obj (F.obj U.unop))) ≫
    O.map (adj.unit.app (F.obj U.unop)).op = φ.app U
  rw [← Category.assoc, hφ, Category.assoc, ← CategoryTheory.Functor.map_comp, h, op_id]
  simp

/-- `counitRingHom` followed by the transpose of `φ`, read at `F U`, is `φ` as a morphism of
presheaves of rings. -/
theorem counitRingHom_comp_transposeRingHom :
    counitRingHom adj (O₀ := O₀) ≫ Functor.whiskerLeft F.op
      (Stacks.PullbackModel.toRingCat (transposeRingHom adj φ)) =
        Functor.whiskerRight φ (forget₂ CommRingCat RingCat) := by
  calc _ = Functor.whiskerRight (Functor.whiskerRight (NatTrans.op adj.counit) O₀ ≫
          Functor.whiskerLeft F.op (transposeRingHom adj φ)) (forget₂ CommRingCat RingCat) := by
        rw [Functor.whiskerRight_comp]; rfl
    _ = _ := by rw [whiskerRight_counit_comp_transposeRingHom]

/-- `φ`, read as a morphism of presheaves of rings. -/
abbrev ringHom :
    O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- **The concrete pullback is left adjoint to the pushforward along `φ`**, the pushforward being
taken along any morphism of presheaves of rings `φ'` equal to `φ` read on rings. -/
def modelAdjunction
    (φ' : O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat)
    (h : ringHom φ = φ') :
    pullbackModel adj φ ⊣ _root_.PresheafOfModules.pushforward.{w} φ' :=
  ((restrictionAdjunction adj).comp
    (Stacks.PullbackModel.extendScalarsAdjunction (transposeRingHom adj φ))).ofNatIsoRight
    (show _root_.PresheafOfModules.restrictScalars.{w}
          (Stacks.PullbackModel.toRingCat (transposeRingHom adj φ)) ⋙
        _root_.PresheafOfModules.pushforward.{w} (counitRingHom adj (O₀ := O₀)) ≅
      _root_.PresheafOfModules.pushforward.{w} φ' from
    Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{w} (Iso.refl F)
      (φ := counitRingHom adj (O₀ := O₀) ≫ Functor.whiskerLeft F.op
        (Stacks.PullbackModel.toRingCat (transposeRingHom adj φ))) (ψ := φ')
      (by
        rw [counitRingHom_comp_transposeRingHom, ← h]
        refine NatTrans.ext (funext fun X => ?_)
        change _ ≫ (O ⋙ forget₂ CommRingCat RingCat).map (𝟙 _) = _
        rw [CategoryTheory.Functor.map_id, Category.comp_id]))

/-- **The counit of the concrete adjunction, on pure tensors**: `1 ⊗ n ↦ N(V ⟶ F (L V)) n` for
`n ∈ N(F (L V))`. -/
theorem modelAdjunction_counit_app_app_tmul
    (φ' : O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat)
    (h : ringHom φ = φ') (N : _root_.PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (V : Dᵒᵖ) (n : N.obj (op (F.obj (L.obj V.unop)))) :
    ((modelAdjunction adj φ φ' h).counit.app N).app V
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom 1 n) =
      N.map (adj.unit.app V.unop).op n := by
  unfold modelAdjunction
  rw [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Adjunction.comp_counit_app]
  have e1 : ∀ x : N.obj V, ((Stacks.PullbackModel.extendScalarsAdjunction
      (transposeRingHom adj φ)).counit.app N).app V
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom 1 x) = x :=
    fun x => Stacks.PullbackModel.transposeApp_tmul (transposeRingHom adj φ) (𝟙 _) V x
  have e2 : N.map (𝟙 (op (F.obj (L.obj V.unop)))) n = n :=
    _root_.PresheafOfModules.map_id_apply N _ n
  change ((Stacks.PullbackModel.extendScalarsAdjunction
      (transposeRingHom adj φ)).counit.app N).app V
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom 1
          (N.map (adj.unit.app V.unop).op (N.map (𝟙 (op (F.obj (L.obj V.unop)))) n))) = _
  exact (e1 _).trans (congrArg (N.map (adj.unit.app V.unop).op) e2)

/-- The pushforward of presheaves of modules along `φ` is a right adjoint, with no smallness
assumption on the two categories. -/
theorem isRightAdjoint_pushforward (adj : L ⊣ F) (φ : O₀ ⟶ F.op ⋙ O)
    (φ' : O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat)
    (h : ringHom φ = φ') :
    (_root_.PresheafOfModules.pushforward.{w} φ').IsRightAdjoint :=
  (modelAdjunction adj φ φ' h).isRightAdjoint

/-- The concrete pullback of a morphism, objectwise: extension of scalars along
`O₀(L V) ⟶ O(V)` of the component at `L V`. -/
theorem pullbackModel_map_app
    {M N : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) (V : Dᵒᵖ) :
    ((pullbackModel adj φ).map f).app V =
      (ModuleCat.extendScalars ((transposeRingHom adj φ).app V).hom).map
        (f.app (op (L.obj V.unop))) := rfl

/-- **Over an object where the transposed ring map is flat, the concrete pullback of an injective
morphism is injective.** -/
theorem injective_pullbackModel_map_app
    {M N : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, Function.Injective (f.app U).hom) (V : Dᵒᵖ)
    (hV : ((transposeRingHom adj φ).app V).hom.Flat) :
    Function.Injective (((pullbackModel adj φ).map f).app V).hom := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{_, _, w}
      ((transposeRingHom adj φ).app V).hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hV
  have : Mono (f.app (op (L.obj V.unop))) := (ModuleCat.mono_iff_injective _).2 (hf _)
  exact (ModuleCat.mono_iff_injective _).1
    (Functor.map_mono (ModuleCat.extendScalars ((transposeRingHom adj φ).app V).hom)
      (f.app (op (L.obj V.unop))))

/-- **The concrete pullback of an objectwise injective morphism is locally injective** as soon as
every object of `D` is covered by objects over which the transposed ring map is flat. -/
theorem isLocallyInjective_pullbackModel_map (K : GrothendieckTopology D)
    (hflat : ∀ V : D, Sieve.generate
      (fun W (_ : W ⟶ V) => ((transposeRingHom adj φ).app (op W)).hom.Flat) ∈ K V)
    {M N : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, Function.Injective (f.app U).hom) :
    Presheaf.IsLocallyInjective K
      ((_root_.PresheafOfModules.toPresheaf _).map ((pullbackModel adj φ).map f)) := by
  refine ⟨fun {V} x y hxy => K.superset_covering ((Sieve.generate_le_iff _ _).2 ?_) (hflat V.unop)⟩
  intro W g hW
  rw [Presheaf.equalizerSieve_apply]
  change (((pullbackModel adj φ).map f).app V).hom x =
    (((pullbackModel adj φ).map f).app V).hom y at hxy
  apply injective_pullbackModel_map_app adj φ f hf (op W) hW
  have hrel := congrArg (((pullbackModel adj φ).obj N).map g.op).hom hxy
  rwa [← _root_.PresheafOfModules.naturality_apply ((pullbackModel adj φ).map f) g.op x,
    ← _root_.PresheafOfModules.naturality_apply ((pullbackModel adj φ).map f) g.op y] at hrel

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {L : D ⥤ C} (adj : L ⊣ F)
  {O₀ : Sheaf J CommRingCat.{w}} {O : Sheaf K CommRingCat.{w}}
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf O₀ ⟶
    (F.sheafPushforwardContinuous RingCat.{w} J K).obj (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- `φ`, read as a morphism of presheaves of commutative rings. -/
def commRingHom : O₀.obj ⟶ F.op ⋙ O.obj where
  app U := CommRingCat.ofHom (R := O₀.obj.obj U) (S := O.obj.obj (op (F.obj U.unop)))
    (φ.hom.app U).hom
  naturality U V f := by
    ext x
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) x

/-- `commRingHom φ`, read as a morphism of presheaves of rings, is the underlying morphism of
`φ`. -/
theorem ringHom_commRingHom : ringHom (commRingHom φ) = φ.hom := rfl

/-- The pushforward of presheaves of modules along the underlying morphism of `φ` is a right
adjoint. -/
theorem isRightAdjoint_presheafPushforward (adj : L ⊣ F) :
    (_root_.PresheafOfModules.pushforward.{w} φ.hom).IsRightAdjoint :=
  isRightAdjoint_pushforward adj (commRingHom φ) φ.hom (ringHom_commRingHom φ)

/-- The pushforward of sheaves of modules along `φ` is a right adjoint. -/
theorem isRightAdjoint_sheafPushforward (adj : L ⊣ F)
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (_root_.SheafOfModules.pushforward.{w} φ).IsRightAdjoint :=
  have := isRightAdjoint_presheafPushforward φ adj
  inferInstance

variable [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(_root_.SheafOfModules.pushforward.{w} φ).IsRightAdjoint]

/-- **The pullback of sheaves of modules along `φ` is the sheafification of the concrete
pullback** `M ↦ (V ↦ O(V) ⊗_{O₀(L V)} M(L V))`. -/
def pullbackIsoSheafifyModel :
    _root_.SheafOfModules.pullback.{w} φ ≅
      _root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₀) ⋙
        pullbackModel adj (commRingHom φ) ⋙
        _root_.PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
  have := isRightAdjoint_presheafPushforward φ adj
  _root_.SheafOfModules.pullbackIso φ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      ((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{w} φ.hom).leftAdjointUniq
        (modelAdjunction adj (commRingHom φ) φ.hom (ringHom_commRingHom φ))) _)

/-- **The pullback of sheaves of modules along `φ` preserves monomorphisms** as soon as every
object of `D` is covered by objects `W` with `O₀(L W) ⟶ O(W)` flat. -/
theorem preservesMonomorphisms_pullback
    (hflat : ∀ V : D, Sieve.generate
      (fun W (_ : W ⟶ V) => ((transposeRingHom adj (commRingHom φ)).app (op W)).hom.Flat) ∈ K V) :
    (_root_.SheafOfModules.pullback.{w} φ).PreservesMonomorphisms := by
  have hT : (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₀) ⋙
        pullbackModel adj (commRingHom φ) ⋙
      _root_.PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).PreservesMonomorphisms := by
    refine ⟨fun f _ => ?_⟩
    have : PreservesFiniteLimits (_root_.SheafOfModules.forget.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
      SheafOfModules.Finite.forgetPreservesFiniteLimits _
    have hm : Mono ((_root_.SheafOfModules.forget.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O₀)).map f) := Functor.map_mono _ f
    exact Stacks.SheafOfModules.FlatSheafification.moduleSheafification_map_mono_of_locallyInjective
      K (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) _
      (isLocallyInjective_pullbackModel_map adj (commRingHom φ) K hflat f.val
        fun U => @_root_.PresheafOfModules.injective_of_mono _ _ _ _ _ _ hm U)
  exact Functor.PreservesMonomorphisms.of_iso (pullbackIsoSheafifyModel adj φ).symm

/-- **The pullback of sheaves of modules along `φ` is exact** as soon as every object of `D` is
covered by objects `W` with `O₀(L W) ⟶ O(W)` flat. -/
theorem preservesFiniteLimits_pullback
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}]
    (hflat : ∀ V : D, Sieve.generate
      (fun W (_ : W ⟶ V) => ((transposeRingHom adj (commRingHom φ)).app (op W)).hom.Flat) ∈ K V) :
    PreservesFiniteLimits (_root_.SheafOfModules.pullback.{w} φ) := by
  let adj' := _root_.SheafOfModules.pullbackPushforwardAdjunction.{w} φ
  have : (_root_.SheafOfModules.pushforward.{w} φ).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : (_root_.SheafOfModules.pullback.{w} φ).Additive := adj'.left_adjoint_additive
  have : (_root_.SheafOfModules.pullback.{w} φ).PreservesMonomorphisms :=
    preservesMonomorphisms_pullback adj φ hflat
  have : PreservesColimits (_root_.SheafOfModules.pullback.{w} φ) :=
    adj'.leftAdjoint_preservesColimits
  have : (_root_.SheafOfModules.pullback.{w} φ).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end Sheaf

end Stacks.PullbackLeftAdjoint

end
