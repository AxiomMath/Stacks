module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageBridgeCoherence

/-!
# The pseudococone coherence of the stage bridge of [Stacks, Tag 0EXD]

Let `f : X ⟶ Y` be a morphism of schemes in characteristic `p`.  The stage functors of
[Stacks, Tag 0EXB], extension of scalars along the coprojections `𝒪 ⟶ colim_F 𝒪`, commute with
the transition functors of [Stacks, Tag 0EXE] by
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso`.  This file proves that these commutations
are compatible with the cocone comparisons `F^* ⋙ S_{n+1} ≅ S_n` of the stage functors and with
the commutation `AlgebraicGeometry.frobeniusVectPullbackIso` of Frobenius with restriction, i.e.
that the family `(frobeniusStageFunctor n, frobeniusStageFunctorPullbackIso n)` is a morphism of
`CategoryTheory.EndoColim.Pseudococone`s, and draws the consequence the essential surjectivity
half of [Stacks, Tag 0EXD] needs: the Frobenius twist of a triple of ordinary modules can be
lowered to `0`.

## Main results

* `AlgebraicGeometry.frobeniusStageBridge_coherence`: **the one-step coherence on all sheaves of
  modules** — the equation `coh1` of the roadmap in
  `StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean`.
* `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_compat` and
  `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_iterIso`: the same on finite locally free
  modules, one step at a time and iterated.
* `AlgebraicGeometry.frobeniusColimitStageTripleUntwistIso`:
  **`frobeniusColimitStageTriple n j Ec Em ψ ≅ frobeniusColimitStageTriple (n + j) 0 (F^{j,*}Ec)
  (F^{j,*}Em) φ`**, with `φ = AlgebraicGeometry.frobeniusStageTripleUntwist … ψ`, and its
  consequence `AlgebraicGeometry.exists_frobeniusColimitStageTriple_zero_iso`: every object of the
  fibre product is attached to a triple of ordinary modules at twist `0`.
* `CategoryTheory.EndoColim.Pseudococone.map_iterObjIso_hom_comp`: a one-step morphism of
  pseudococones is compatible with the iterated comparisons.

## Implementation notes

The coherence is an equation between five comparisons of left adjoints, built from
`SheafOfModules.pullbackComp`, transports `eqToIso` and `Adjunction.leftAdjointUniq`.
`AlgebraicGeometry.frobeniusStageBridge_natTrans_square` reduces it to the mirrored equation of the
`conjugateEquiv` mates, which are natural transformations between composites of pushforwards.
Rather than computing the mates as explicit composites — which would need rewriting at the
concrete sites, where the composite site functors `Opens.map (𝟙 Y) ⋙ Opens.map f.base` and
`Opens.map f.base ⋙ Opens.map (𝟙 X)` agree only definitionally — each mate is shown to *become an
`eqToHom`* after the faithful functor `Stacks.SheafOfModules.underlying` to presheaves of abelian
groups (`CategoryTheory.NatTrans.IsEqToHomAfter`).  That property is stable under composition,
whiskering and associators, so both sides of the mirrored equation have it, and two such
transformations with the same source and target are equal.  The only computation of a mate that is
needed is at abstract sites
(`Stacks.SheafOfModules.conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm`), where the two
composite site functors are related by a hypothesis `F₁ ⋙ G₁ = F₂ ⋙ G₂`; at the concrete
morphisms that hypothesis is `rfl`.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe v u

namespace CategoryTheory.NatTrans

variable {A : Type*} [Category A] {B : Type*} [Category B] {C : Type*} [Category C]

/-- `θ` becomes an `eqToHom` once whiskered by `K`. -/
def IsEqToHomAfter (K : B ⥤ C) {R R' : A ⥤ B} (θ : R ⟶ R') : Prop :=
  ∃ h : R ⋙ K = R' ⋙ K, Functor.whiskerRight θ K = eqToHom h

namespace IsEqToHomAfter

variable {K : B ⥤ C} {R R' R'' : A ⥤ B}

/-- An identity becomes an identity, i.e. `eqToHom rfl`, after any functor. -/
theorem id (R : A ⥤ B) : IsEqToHomAfter K (𝟙 R) :=
  ⟨rfl, by ext; simp⟩

/-- An `eqToHom` stays an `eqToHom` after any functor. -/
theorem eqToHom (h : R = R') : IsEqToHomAfter K (eqToHom h) := by
  subst h
  exact id R

/-- A composite of two transformations which become `eqToHom`s becomes one. -/
theorem comp {θ : R ⟶ R'} {θ' : R' ⟶ R''} (hθ : IsEqToHomAfter K θ)
    (hθ' : IsEqToHomAfter K θ') : IsEqToHomAfter K (θ ≫ θ') := by
  obtain ⟨h, e⟩ := hθ
  obtain ⟨h', e'⟩ := hθ'
  exact ⟨h.trans h', by rw [Functor.whiskerRight_comp, e, e', eqToHom_trans]⟩

/-- Whiskering on the left preserves becoming an `eqToHom`. -/
theorem whiskerLeft {A' : Type*} [Category A'] (G : A' ⥤ A) {θ : R ⟶ R'}
    (hθ : IsEqToHomAfter K θ) : IsEqToHomAfter K (Functor.whiskerLeft G θ) := by
  obtain ⟨h, e⟩ := hθ
  refine ⟨congrArg (G ⋙ ·) h, ?_⟩
  ext X
  have := NatTrans.congr_app e (G.obj X)
  simpa [eqToHom_app] using this

/-- A transformation which becomes an `eqToHom` after `K` does so after `K ⋙ Ψ` too. -/
theorem postcomp {C' : Type*} [Category C'] (Ψ : C ⥤ C') {θ : R ⟶ R'}
    (hθ : IsEqToHomAfter K θ) : IsEqToHomAfter (K ⋙ Ψ) θ := by
  obtain ⟨h, e⟩ := hθ
  refine ⟨congrArg (· ⋙ Ψ) h, ?_⟩
  ext X
  have := congrArg Ψ.map (NatTrans.congr_app e X)
  simpa [eqToHom_app, eqToHom_map] using this

/-- Transport along an equality of the functor applied afterwards. -/
theorem of_eq {K' : B ⥤ C} (hK : K = K') {θ : R ⟶ R'} (hθ : IsEqToHomAfter K θ) :
    IsEqToHomAfter K' θ := by
  subst hK
  exact hθ

/-- Whiskering on the right by `H` turns becoming an `eqToHom` after `H ⋙ K` into becoming one
after `K`. -/
theorem whiskerRight {B' : Type*} [Category B'] (H : B ⥤ B') {K : B' ⥤ C} {θ : R ⟶ R'}
    (hθ : IsEqToHomAfter (H ⋙ K) θ) : IsEqToHomAfter K (Functor.whiskerRight θ H) := by
  obtain ⟨h, e⟩ := hθ
  exact ⟨h, by ext X; simpa using NatTrans.congr_app e X⟩

/-- The associator becomes an `eqToHom` after any functor. -/
theorem associator_hom {A₁ A₂ : Type*} [Category A₁] [Category A₂] (F : A ⥤ A₁)
    (G : A₁ ⥤ A₂) (H : A₂ ⥤ B) : IsEqToHomAfter K (Functor.associator F G H).hom :=
  id _

/-- The inverse associator becomes an `eqToHom` after any functor. -/
theorem associator_inv {A₁ A₂ : Type*} [Category A₁] [Category A₂] (F : A ⥤ A₁)
    (G : A₁ ⥤ A₂) (H : A₂ ⥤ B) : IsEqToHomAfter K (Functor.associator F G H).inv :=
  id _

/-- Two natural transformations that become `eqToHom`s after a faithful functor are equal. -/
theorem ext [K.Faithful] {θ θ' : R ⟶ R'} (hθ : IsEqToHomAfter K θ)
    (hθ' : IsEqToHomAfter K θ') : θ = θ' := by
  obtain ⟨h, e⟩ := hθ
  obtain ⟨h', e'⟩ := hθ'
  ext X
  exact K.map_injective (NatTrans.congr_app (e.trans e'.symm) X)

end IsEqToHomAfter

end CategoryTheory.NatTrans

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **The mate of an `eqToIso` followed by a `leftAdjointUniq` becomes an `eqToHom`** as soon as
the right-adjoint replacement `e` does and the mate of the `eqToHom` does.  This is the shape of
`AlgebraicGeometry.frobeniusPullbackStageIso`. -/
theorem isEqToHomAfter_conjugateEquiv_eqToIso_trans_leftAdjointUniq {E : Type*} [Category E]
    {K : C ⥤ E} {L₁ L₂ Lₘ : C ⥤ D} {R₁ R₂ Rₘ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adjₘ : Lₘ ⊣ Rₘ)
    (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ Rₘ) (h : L₂ = Lₘ) (he : NatTrans.IsEqToHomAfter K e.hom)
    (hh : NatTrans.IsEqToHomAfter K (conjugateEquiv adjₘ adj₂ (eqToHom h))) :
    NatTrans.IsEqToHomAfter K
      (conjugateEquiv adj₁ adj₂
        (eqToIso h ≪≫ leftAdjointUniq adjₘ (adj₁.ofNatIsoRight e)).hom) := by
  rw [Iso.trans_hom, eqToIso.hom, ← conjugateEquiv_comp adj₁ adjₘ adj₂,
    Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom]
  exact he.comp hh

end CategoryTheory.Adjunction

namespace CategoryTheory.EndoColim

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₁} C']
  {D : Type u₃} [Category.{v₂} D] {D' : Type u₄} [Category.{v₃} D']
  {F : C ⥤ C} {F' : C' ⥤ C'} (P : Pseudococone F D) (P' : Pseudococone F' D')
  (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (Ψ : D ⥤ D')
  (β : ∀ n, P.stage n ⋙ Ψ ≅ Φ ⋙ P'.stage n)

/-- **The comparison of a morphism of pseudo-cocones with the iterated comparisons.** -/
theorem Pseudococone.map_iterObjIso_hom_comp
    (hβ : ∀ (n : ℕ) (E : C), Ψ.map ((P.compat n).hom.app E) ≫ (β n).hom.app E =
      (β (n + 1)).hom.app (F.obj E) ≫ (P'.stage (n + 1)).map (α.hom.app E) ≫
        (P'.compat n).hom.app (Φ.obj E))
    (n : ℕ) : ∀ (k : ℕ) (E : C),
    Ψ.map (P.iterObjIso n k E).hom ≫ (β n).hom.app E =
      (β (n + k)).hom.app ((F.endoIter k).obj E) ≫
        (P'.stage (n + k)).map (squareIter F F' Φ α k E).inv ≫
          (P'.iterObjIso n k (Φ.obj E)).hom
  | 0, E => by
      simp [Pseudococone.iterObjIso]
  | k + 1, E => by
      have h₁ := hβ (n + k) ((F.endoIter k).obj E)
      have h₂ := (P'.compat (n + k)).hom.naturality (squareIter F F' Φ α k E).inv
      have ih := Pseudococone.map_iterObjIso_hom_comp hβ n k E
      simp only [Functor.comp_map] at h₂
      change Ψ.map ((P.compat (n + k)).hom.app ((F.endoIter k).obj E) ≫
            (P.iterObjIso n k E).hom) ≫ (β n).hom.app E =
        (β (n + k + 1)).hom.app (F.obj ((F.endoIter k).obj E)) ≫
          (P'.stage (n + k + 1)).map (α.hom.app ((F.endoIter k).obj E) ≫
            F'.map (squareIter F F' Φ α k E).inv) ≫
            (P'.compat (n + k)).hom.app ((F'.endoIter k).obj (Φ.obj E)) ≫
              (P'.iterObjIso n k (Φ.obj E)).hom
      rw [Functor.map_comp, Category.assoc, ih, reassoc_of% h₁, Functor.map_comp,
        Category.assoc, reassoc_of% h₂]

end CategoryTheory.EndoColim

namespace Stacks.SheafOfModules

section Bridge

variable {C : Type*} [Category C] {D₁ : Type*} [Category D₁] {D₂ : Type*} [Category D₂]
  {E : Type*} [Category E]
  {J : GrothendieckTopology C} {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂}
  {L : GrothendieckTopology E}
  {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ E} {F₂ : C ⥤ D₂} {G₂ : D₂ ⥤ E}
  {S : Sheaf J RingCat.{u}} {R₁ : Sheaf K₁ RingCat.{u}} {R₂ : Sheaf K₂ RingCat.{u}}
  {T : Sheaf L RingCat.{u}}
  [Functor.IsContinuous F₁ J K₁] [Functor.IsContinuous G₁ K₁ L]
  [Functor.IsContinuous (F₁ ⋙ G₁) J L]
  [Functor.IsContinuous F₂ J K₂] [Functor.IsContinuous G₂ K₂ L]
  [Functor.IsContinuous (F₂ ⋙ G₂) J L]

/-- **The mate of a contraction of an iterated pullback, followed by a transport and the inverse
of another contraction**, computed factor by factor: it is the contraction of the iterated
pushforward, the mate `β` of the transport, and the inverse contraction of the other iterated
pushforward.  This is the shape of the stage bridge
`AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` and of
`AlgebraicGeometry.modulesPullbackSquareIso`. -/
theorem conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm
    (φ₁ : S ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).obj R₁)
    (ψ₁ : R₁ ⟶ (G₁.sheafPushforwardContinuous RingCat.{u} K₁ L).obj T)
    (φ₂ : S ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).obj R₂)
    (ψ₂ : R₂ ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} K₂ L).obj T)
    [(_root_.SheafOfModules.pushforward.{v} φ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} φ₂).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ₂).IsRightAdjoint]
    (hL : _root_.SheafOfModules.pullback.{v} (F := F₁ ⋙ G₁)
        (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁) =
      _root_.SheafOfModules.pullback.{v} (F := F₂ ⋙ G₂)
        (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂))
    (β : _root_.SheafOfModules.pushforward.{v} (F := F₂ ⋙ G₂)
        (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂) ⟶
      _root_.SheafOfModules.pushforward.{v} (F := F₁ ⋙ G₁)
        (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁))
    (hβ : conjugateEquiv
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} (F := F₂ ⋙ G₂)
          (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂))
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} (F := F₁ ⋙ G₁)
          (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁))
        (eqToHom hL) = β) :
    conjugateEquiv
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₂).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ₂))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₁).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ₁))
        (_root_.SheafOfModules.pullbackComp.{v} φ₁ ψ₁ ≪≫ eqToIso hL ≪≫
          (_root_.SheafOfModules.pullbackComp.{v} φ₂ ψ₂).symm).hom =
      (_root_.SheafOfModules.pushforwardComp.{v} φ₂ ψ₂).hom ≫ β ≫
        (_root_.SheafOfModules.pushforwardComp.{v} φ₁ ψ₁).inv := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    ← conjugateEquiv_comp _ (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
      (F := F₁ ⋙ G₁) (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁)),
    ← conjugateEquiv_comp _ (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
      (F := F₂ ⋙ G₂) (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂)),
    _root_.SheafOfModules.conjugateEquiv_pullbackComp_inv, hβ, Category.assoc]
  congr 2
  exact congrArg Iso.hom (conjugateIsoEquiv_pullbackComp φ₁ ψ₁)

end Bridge

section Underlying

open CategoryTheory.NatTrans

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}

variable (S) in
/-- The underlying presheaf of abelian groups of a sheaf of modules. -/
abbrev underlying : _root_.SheafOfModules.{v} S ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  _root_.SheafOfModules.forget.{v} S ⋙ PresheafOfModules.toPresheaf.{v} S.obj

/-- On underlying presheaves of abelian groups, pushforward of sheaves of modules is
precomposition with the site functor. -/
theorem pushforward_comp_underlying {F : C ⥤ D} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    _root_.SheafOfModules.pushforward.{v} φ ⋙ underlying.{v} S =
      underlying.{v} R ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  rfl

/-- Whiskering by a pushforward preserves becoming an `eqToHom` on underlying presheaves. -/
theorem isEqToHomAfter_whiskerRight_pushforward {F : C ⥤ D} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {A : Type*} [Category A] {P P' : A ⥤ _root_.SheafOfModules.{v} R} {θ : P ⟶ P'}
    (hθ : IsEqToHomAfter (underlying.{v} R) θ) :
    IsEqToHomAfter (underlying.{v} S)
      (Functor.whiskerRight θ (_root_.SheafOfModules.pushforward.{v} φ)) :=
  IsEqToHomAfter.whiskerRight _
    ((hθ.postcomp _).of_eq (pushforward_comp_underlying φ).symm)

/-- **The mate of a transport between pullbacks along equal morphisms of sheaves of rings is an
`eqToHom` on underlying presheaves.**  The two morphisms may live over two site functors which are
merely equal, which is the situation of the composites `Opens.map (𝟙 Y) ⋙ Opens.map f.base` and
`Opens.map f.base ⋙ Opens.map (𝟙 X)`. -/
theorem isEqToHomAfter_conjugateEquiv_eqToHom_pullback {F₁ F₂ : C ⥤ D}
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ J K] (hF : F₁ = F₂)
    {φ₁ : S ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    {φ₂ : S ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj R} (hφ : HEq φ₁ φ₂)
    [(_root_.SheafOfModules.pushforward.{v} φ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} φ₂).IsRightAdjoint]
    (hL : _root_.SheafOfModules.pullback.{v} φ₁ = _root_.SheafOfModules.pullback.{v} φ₂) :
    IsEqToHomAfter (underlying.{v} S)
      (conjugateEquiv (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₂)
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₁) (eqToHom hL)) := by
  subst hF
  cases hφ
  rw [eqToHom_refl, conjugateEquiv_id]
  exact IsEqToHomAfter.id _

/-- The variant of
`Stacks.SheafOfModules.isEqToHomAfter_conjugateEquiv_eqToHom_pullback` with a further adjunction
composed on the right of both. -/
theorem isEqToHomAfter_conjugateEquiv_eqToHom_pullback_comp {F₁ F₂ : C ⥤ D}
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ J K] (hF : F₁ = F₂)
    {φ₁ : S ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    {φ₂ : S ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj R} (hφ : HEq φ₁ φ₂)
    [(_root_.SheafOfModules.pushforward.{v} φ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} φ₂).IsRightAdjoint]
    {E : Type*} [Category E] {L : _root_.SheafOfModules.{v} R ⥤ E}
    {G : E ⥤ _root_.SheafOfModules.{v} R} (adj : L ⊣ G)
    (hL : _root_.SheafOfModules.pullback.{v} φ₁ ⋙ L =
      _root_.SheafOfModules.pullback.{v} φ₂ ⋙ L) :
    IsEqToHomAfter (underlying.{v} S)
      (conjugateEquiv ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₂).comp adj)
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₁).comp adj)
        (eqToHom hL)) := by
  subst hF
  cases hφ
  rw [eqToHom_refl, conjugateEquiv_id]
  exact IsEqToHomAfter.id _

/-- The contraction of an iterated pushforward is an identity on underlying presheaves. -/
theorem isEqToHomAfter_pushforwardComp_hom {D' : Type*} [Category D']
    {K' : GrothendieckTopology D'} {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
    {F : C ⥤ D} [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R') :
    IsEqToHomAfter (underlying.{v} S) (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).hom :=
  IsEqToHomAfter.id _

/-- The inverse contraction of an iterated pushforward is an identity on underlying presheaves. -/
theorem isEqToHomAfter_pushforwardComp_inv {D' : Type*} [Category D']
    {K' : GrothendieckTopology D'} {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
    {F : C ⥤ D} [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R') :
    IsEqToHomAfter (underlying.{v} S) (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).inv :=
  IsEqToHomAfter.id _

end Underlying

section BridgeUnderlying

open CategoryTheory.NatTrans

variable {C : Type*} [Category C] {D₁ : Type*} [Category D₁] {D₂ : Type*} [Category D₂]
  {E : Type*} [Category E]
  {J : GrothendieckTopology C} {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂}
  {L : GrothendieckTopology E}
  {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ E} {F₂ : C ⥤ D₂} {G₂ : D₂ ⥤ E}
  {S : Sheaf J RingCat.{u}} {R₁ : Sheaf K₁ RingCat.{u}} {R₂ : Sheaf K₂ RingCat.{u}}
  {T : Sheaf L RingCat.{u}}
  [Functor.IsContinuous F₁ J K₁] [Functor.IsContinuous G₁ K₁ L]
  [Functor.IsContinuous (F₁ ⋙ G₁) J L]
  [Functor.IsContinuous F₂ J K₂] [Functor.IsContinuous G₂ K₂ L]
  [Functor.IsContinuous (F₂ ⋙ G₂) J L]

/-- **The mate of a contraction, a transport between pullbacks along equal composite morphisms of
sheaves of rings, and an inverse contraction is an `eqToHom` on underlying presheaves.** -/
theorem isEqToHomAfter_conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm
    (φ₁ : S ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).obj R₁)
    (ψ₁ : R₁ ⟶ (G₁.sheafPushforwardContinuous RingCat.{u} K₁ L).obj T)
    (φ₂ : S ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).obj R₂)
    (ψ₂ : R₂ ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} K₂ L).obj T)
    [(_root_.SheafOfModules.pushforward.{v} φ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ₁).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} φ₂).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ₂).IsRightAdjoint]
    (hF : F₁ ⋙ G₁ = F₂ ⋙ G₂)
    (hφ : HEq (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁)
      (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂))
    (hL : _root_.SheafOfModules.pullback.{v} (F := F₁ ⋙ G₁)
        (φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁) =
      _root_.SheafOfModules.pullback.{v} (F := F₂ ⋙ G₂)
        (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂)) :
    IsEqToHomAfter (underlying.{v} S)
      (conjugateEquiv
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₂).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ₂))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ₁).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ₁))
        (_root_.SheafOfModules.pullbackComp.{v} φ₁ ψ₁ ≪≫ eqToIso hL ≪≫
          (_root_.SheafOfModules.pullbackComp.{v} φ₂ ψ₂).symm).hom) := by
  rw [conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm φ₁ ψ₁ φ₂ ψ₂ hL _ rfl]
  have h₁ := isEqToHomAfter_conjugateEquiv_eqToHom_pullback.{v} (F₁ := F₁ ⋙ G₁) (F₂ := F₂ ⋙ G₂)
    (φ₁ := φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J K₁).map ψ₁)
    (φ₂ := φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} J K₂).map ψ₂) hF hφ hL
  exact (isEqToHomAfter_pushforwardComp_hom φ₂ ψ₂).comp
    (h₁.comp
      (isEqToHomAfter_pushforwardComp_inv φ₁ ψ₁))

end BridgeUnderlying

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]

open CategoryTheory.NatTrans Stacks.SheafOfModules in
/-- **The mate of the stage bridge is an identity on underlying presheaves.** -/
theorem isEqToHomAfter_conjugateEquiv_frobeniusStageExtendScalarsPullbackIso (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) :
    IsEqToHomAfter (underlying.{u} Y.ringSheafOnOpens)
      (conjugateEquiv
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (frobeniusStageStructureMap X p hX n)))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (frobeniusStageStructureMap Y p hY n)).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (frobeniusColimitStructureSheafHom p f hX hY)))
        (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom) :=
  isEqToHomAfter_conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm
    (frobeniusStageStructureMap Y p hY n) (frobeniusColimitStructureSheafHom p f hX hY)
    f.ringSheafOnOpensHom (frobeniusStageStructureMap X p hX n) rfl
    (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n))
    (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ)
      (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n))

open CategoryTheory.NatTrans Stacks.SheafOfModules in
/-- **The mate of the cocone compatibility of the stage functors is an identity on underlying
presheaves.** -/
theorem isEqToHomAfter_conjugateEquiv_frobeniusPullbackStageIso (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (n : ℕ) :
    IsEqToHomAfter (underlying.{u} X.ringSheafOnOpens)
      (conjugateEquiv
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusStageStructureMap X p hX n))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (absoluteFrobenius X p hX).ringSheafOnOpensHom).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (frobeniusStageStructureMap X p hX (n + 1))))
        (frobeniusPullbackStageIso X p hX n).hom) :=
  Adjunction.isEqToHomAfter_conjugateEquiv_eqToIso_trans_leftAdjointUniq _ _ _ _ _
    (IsEqToHomAfter.eqToHom (pushforward_frobeniusStage_comp X p hX n).symm)
    (isEqToHomAfter_conjugateEquiv_eqToHom_pullback_comp.{u}
      (F₁ := Opens.map (absoluteFrobenius X p hX).base) (F₂ := Opens.map (𝟙 _))
      (φ₁ := (absoluteFrobenius X p hX).ringSheafOnOpensHom)
      (φ₂ := frobeniusSelfStructureMap X p hX) rfl
      (heq_of_eq (toRingCatSheafHom_absoluteFrobenius X p hX)) _ _)

open CategoryTheory.NatTrans Stacks.SheafOfModules in
/-- **The mate of the commutation of Frobenius with restriction is an identity on underlying
presheaves.** -/
theorem isEqToHomAfter_conjugateEquiv_frobeniusModulesPullbackIso (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    IsEqToHomAfter (underlying.{u} Y.ringSheafOnOpens)
      (conjugateEquiv
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (absoluteFrobenius X p hX).ringSheafOnOpensHom))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
            (absoluteFrobenius Y p hY).ringSheafOnOpensHom).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom))
        (frobeniusModulesPullbackIso f p hX hY).hom) :=
  isEqToHomAfter_conjugateEquiv_pullbackComp_trans_eqToIso_trans_symm
    (absoluteFrobenius Y p hY).ringSheafOnOpensHom f.ringSheafOnOpensHom
    f.ringSheafOnOpensHom (absoluteFrobenius X p hX).ringSheafOnOpensHom rfl
    (congr_arg_heq (fun g : X ⟶ Y => g.ringSheafOnOpensHom)
      (absoluteFrobenius_naturality f p hX hY).symm) _

open CategoryTheory.NatTrans Stacks.SheafOfModules in
/-- **The pseudococone coherence of the stage bridge of [Stacks, Tag 0EXD]**, on all sheaves of
modules: the equation `coh1` of the roadmap.  The stage comparison of `Y`, carried along the
transition functor, followed by the bridge at the stage `n`, is the bridge at the stage `n + 1`
followed by the commutation of Frobenius with restriction and the stage comparison of `X`.

By `AlgebraicGeometry.frobeniusStageBridge_natTrans_square` it suffices to check the mirrored
equation of the mates, and each of the five mates is an identity on underlying presheaves of
abelian groups, which is faithful. -/
theorem frobeniusStageBridge_coherence (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (n : ℕ) :
    Functor.whiskerRight (frobeniusPullbackStageIso Y p hY n).hom
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hX hY)) ≫
        (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pullback (absoluteFrobenius Y p hY))
            (frobeniusStageExtendScalarsPullbackIso p f hX hY (n + 1)).hom ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (frobeniusModulesPullbackIso f p hX hY).hom
                (frobeniusStageExtendScalars X p hX (n + 1)) ≫
              (Functor.associator _ _ _).hom ≫
                Functor.whiskerLeft (Scheme.Modules.pullback f)
                  (frobeniusPullbackStageIso X p hX n).hom :=
  frobeniusStageBridge_natTrans_square p f hX hY n
    (IsEqToHomAfter.ext
      ((isEqToHomAfter_conjugateEquiv_frobeniusStageExtendScalarsPullbackIso p f hX hY n).comp
        ((isEqToHomAfter_conjugateEquiv_frobeniusPullbackStageIso p Y hY n).whiskerLeft _))
      ((isEqToHomAfter_whiskerRight_pushforward _
          (isEqToHomAfter_conjugateEquiv_frobeniusPullbackStageIso p X hX n)).comp
        ((IsEqToHomAfter.associator_hom _ _ _).comp
          (((isEqToHomAfter_conjugateEquiv_frobeniusModulesPullbackIso p f hX hY).whiskerLeft
              _).comp
            ((IsEqToHomAfter.associator_inv _ _ _).comp
              ((isEqToHomAfter_whiskerRight_pushforward _
                  (isEqToHomAfter_conjugateEquiv_frobeniusStageExtendScalarsPullbackIso
                    p f hX hY (n + 1))).comp
                (IsEqToHomAfter.associator_hom _ _ _)))))))

/-- **The family `(frobeniusStageFunctor n, frobeniusStageFunctorPullbackIso n)` is a morphism of
pseudococones, one step at a time**: `AlgebraicGeometry.frobeniusStageBridge_coherence` on finite
locally free modules. -/
theorem frobeniusStageFunctorPullbackIso_compat (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (n : ℕ) (E : Y.Vect) :
    (frobeniusColimitVectorBundlesPullback p f hX hY).map
        ((frobeniusStageFunctorIso Y p hY n).hom.app E) ≫
      (frobeniusStageFunctorPullbackIso p f hX hY n).hom.app E =
    (frobeniusStageFunctorPullbackIso p f hX hY (n + 1)).hom.app
        ((frobeniusPullback Y p hY).obj E) ≫
      (frobeniusStageFunctor X p hX (n + 1)).map ((frobeniusVectPullbackIso f p hX hY).hom.app E) ≫
        (frobeniusStageFunctorIso X p hX n).hom.app ((Scheme.Vect.pullback f).obj E) := by
  apply (ObjectProperty.ι _).map_injective
  have := NatTrans.congr_app (frobeniusStageBridge_coherence p f hX hY n) E.obj
  simp only [NatTrans.comp_app] at this
  exact this

/-- The iterated Frobenius comparison `F_X^{k,*}(f^*E) ≅ f^*(F_Y^{k,*}E)` of the restriction
along `f`. -/
noncomputable abbrev frobeniusVectPullbackIterIso (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (k : ℕ) (E : Y.Vect) :
    (frobeniusPullbackIter X p hX k).obj ((Scheme.Vect.pullback f).obj E) ≅
      (Scheme.Vect.pullback f).obj ((frobeniusPullbackIter Y p hY k).obj E) :=
  EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
    (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) k E

/-- **The commutation of `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` with
`AlgebraicGeometry.frobeniusStageFunctorIterIso` and the iterated commutation of Frobenius with
restriction.** -/
theorem frobeniusStageFunctorPullbackIso_iterIso (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (n k : ℕ) (E : Y.Vect) :
    (frobeniusColimitVectorBundlesPullback p f hX hY).map
        ((frobeniusStageFunctorIterIso Y p hY n k).hom.app E) ≫
      (frobeniusStageFunctorPullbackIso p f hX hY n).hom.app E =
    (frobeniusStageFunctorPullbackIso p f hX hY (n + k)).hom.app
        ((frobeniusPullbackIter Y p hY k).obj E) ≫
      (frobeniusStageFunctor X p hX (n + k)).map (frobeniusVectPullbackIterIso p f hX hY k E).inv ≫
        (frobeniusStageFunctorIterIso X p hX n k).hom.app ((Scheme.Vect.pullback f).obj E) := by
  have := EndoColim.Pseudococone.map_iterObjIso_hom_comp
    (frobeniusColimitVectPseudococone Y p hY) (frobeniusColimitVectPseudococone X p hX)
    (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
    (frobeniusColimitVectorBundlesPullback p f hX hY)
    (frobeniusStageFunctorPullbackIso p f hX hY)
    (frobeniusStageFunctorPullbackIso_compat p f hX hY) n k E
  rwa [frobeniusColimitVectPseudococone_iterObjIso_hom,
    frobeniusColimitVectPseudococone_iterObjIso_hom] at this

/-- At twist `0` the comparison on Hom-sets is the stage functor itself. -/
theorem frobeniusStageHomMap_zero (X : Scheme.{u}) (hX : IsInCharacteristic X p) (n : ℕ)
    {E G : X.Vect} (g : E ⟶ G) :
    frobeniusStageHomMap X p hX n 0 g = (frobeniusStageFunctor X p hX n).map g :=
  (Category.id_comp _).trans (Category.comp_id _)

section Triple

variable {XZ XM XE : Scheme.{u}} (e : XE ⟶ XZ) (d : XE ⟶ XM)
  (hZ : IsInCharacteristic XZ p) (hM : IsInCharacteristic XM p)
  (hE : IsInCharacteristic XE p)

/-- The isomorphism of the `j`-fold Frobenius pullbacks of the restrictions to `E` read as an
isomorphism of the restrictions of the `j`-fold Frobenius pullbacks: the structural isomorphism
at twist `0` of the triple `(F^{j,*}Ec, F^{j,*}Em)`. -/
noncomputable def frobeniusStageTripleUntwist (j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    (frobeniusPullbackIter XE p hE 0).obj
        ((Scheme.Vect.pullback e).obj ((frobeniusPullbackIter XZ p hZ j).obj Ec)) ≅
      (frobeniusPullbackIter XE p hE 0).obj
        ((Scheme.Vect.pullback d).obj ((frobeniusPullbackIter XM p hM j).obj Em)) :=
  (frobeniusVectPullbackIterIso p e hE hZ j Ec).symm ≪≫ psi ≪≫
    frobeniusVectPullbackIterIso p d hE hM j Em

/-- **The compatibility of the two stage-raising isomorphisms with the structural isomorphisms
of the two triples.** It is the commutation of `AlgebraicGeometry.frobeniusStageFunctorPullbackIso`
with `AlgebraicGeometry.frobeniusStageFunctorIterIso` at the two legs of the cospan. -/
theorem frobeniusColimitStageTripleUntwist_comm (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    (frobeniusColimitVectorBundlesPullback p e hE hZ).map
        ((frobeniusStageFunctorIterIso XZ p hZ n j).hom.app Ec) ≫
      (frobeniusStageFunctorPullbackIso p e hE hZ n).hom.app Ec ≫
        frobeniusStageHomMap XE p hE n j psi.hom ≫
          (frobeniusStageFunctorPullbackIso p d hE hM n).inv.app Em =
    (frobeniusStageFunctorPullbackIso p e hE hZ (n + j)).hom.app
          ((frobeniusPullbackIter XZ p hZ j).obj Ec) ≫
        (frobeniusStageFunctor XE p hE (n + j)).map
          (frobeniusStageTripleUntwist p e d hZ hM hE j Ec Em psi).hom ≫
        (frobeniusStageFunctorPullbackIso p d hE hM (n + j)).inv.app
          ((frobeniusPullbackIter XM p hM j).obj Em) ≫
      (frobeniusColimitVectorBundlesPullback p d hE hM).map
        ((frobeniusStageFunctorIterIso XM p hM n j).hom.app Em) := by
  have hc := frobeniusStageFunctorPullbackIso_iterIso p e hE hZ n j Ec
  have hm := frobeniusStageFunctorPullbackIso_iterIso p d hE hM n j Em
  have hm' : (frobeniusStageFunctorPullbackIso p d hE hM (n + j)).inv.app
        ((frobeniusPullbackIter XM p hM j).obj Em) ≫
      (frobeniusColimitVectorBundlesPullback p d hE hM).map
        ((frobeniusStageFunctorIterIso XM p hM n j).hom.app Em) =
      (frobeniusStageFunctor XE p hE (n + j)).map
          (frobeniusVectPullbackIterIso p d hE hM j Em).inv ≫
        (frobeniusStageFunctorIterIso XE p hE n j).hom.app ((Scheme.Vect.pullback d).obj Em) ≫
          (frobeniusStageFunctorPullbackIso p d hE hM n).inv.app Em := by
    rw [← Iso.app_inv, ← Iso.app_inv, Iso.inv_comp_eq]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv]
    simpa only [Category.assoc, Iso.app_hom] using hm
  have key : (frobeniusStageFunctor XE p hE (n + j)).map
        (frobeniusVectPullbackIterIso p e hE hZ j Ec).inv ≫
      (frobeniusStageFunctorIterIso XE p hE n j).hom.app ((Scheme.Vect.pullback e).obj Ec) ≫
        frobeniusStageHomMap XE p hE n j psi.hom =
      (frobeniusStageFunctor XE p hE (n + j)).map
          (frobeniusStageTripleUntwist p e d hZ hM hE j Ec Em psi).hom ≫
        (frobeniusStageFunctor XE p hE (n + j)).map
          (frobeniusVectPullbackIterIso p d hE hM j Em).inv ≫
        (frobeniusStageFunctorIterIso XE p hE n j).hom.app ((Scheme.Vect.pullback d).obj Em) := by
    have hφ : (frobeniusStageTripleUntwist p e d hZ hM hE j Ec Em psi).hom ≫
        (frobeniusVectPullbackIterIso p d hE hM j Em).inv =
          (frobeniusVectPullbackIterIso p e hE hZ j Ec).inv ≫ psi.hom := by
      simp [frobeniusStageTripleUntwist]
    simp only [frobeniusStageHomMap, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp_assoc, ← hφ]
    exact Functor.map_comp_assoc _ _ _ _
  exact ((reassoc_of% hc) _).trans (congrArg (_ ≫ ·)
    (((reassoc_of% key) _).trans (congrArg (_ ≫ ·) hm'.symm)))

/-- **Lowering the Frobenius twist of a triple of ordinary modules.** The object of the
categorical fibre product attached to `(Ec, Em, ψ)` at stage `n` and twist `j` is isomorphic to
the one attached to `(F^{j,*}Ec, F^{j,*}Em, φ)` at stage `n + j` and twist `0`, where `φ` is `ψ`
read through the iterated commutation of Frobenius with restriction. -/
noncomputable def frobeniusColimitStageTripleUntwistIso (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    frobeniusColimitStageTriple p e d hZ hM hE (n + j) 0
        ((frobeniusPullbackIter XZ p hZ j).obj Ec) ((frobeniusPullbackIter XM p hM j).obj Em)
        (frobeniusStageTripleUntwist p e d hZ hM hE j Ec Em psi) ≅
      frobeniusColimitStageTriple p e d hZ hM hE n j Ec Em psi :=
  CategoricalPullback.mkIso ((frobeniusStageFunctorIterIso XZ p hZ n j).app Ec)
    ((frobeniusStageFunctorIterIso XM p hM n j).app Em)
    ((frobeniusColimitStageTripleUntwist_comm p e d hZ hM hE n j Ec Em psi).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm)

/-- **Every object of the categorical fibre product of [Stacks, Tag 0EXD] is isomorphic to one
attached to a triple of ordinary modules at twist `0`**, the three corners being quasi-compact
and quasi-separated: `AlgebraicGeometry.exists_frobeniusColimitStageTriple_iso` followed by the
twist-lowering isomorphism `AlgebraicGeometry.frobeniusColimitStageTripleUntwistIso`. -/
theorem exists_frobeniusColimitStageTriple_zero_iso
    [CompactSpace XZ] [QuasiSeparatedSpace XZ] [CompactSpace XM] [QuasiSeparatedSpace XM]
    [CompactSpace XE] [QuasiSeparatedSpace XE]
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p d hE hM)) :
    ∃ (n : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
      (φ : (frobeniusPullbackIter XE p hE 0).obj ((Scheme.Vect.pullback e).obj Ec) ≅
        (frobeniusPullbackIter XE p hE 0).obj ((Scheme.Vect.pullback d).obj Em)),
      Nonempty (T ≅ frobeniusColimitStageTriple p e d hZ hM hE n 0 Ec Em φ) := by
  obtain ⟨n, j, Ec, Em, psi, ⟨i⟩⟩ := exists_frobeniusColimitStageTriple_iso p e d hZ hM hE T
  exact ⟨n + j, _, _, _,
    ⟨i ≪≫ (frobeniusColimitStageTripleUntwistIso p e d hZ hM hE n j Ec Em psi).symm⟩⟩

end Triple

end AlgebraicGeometry
