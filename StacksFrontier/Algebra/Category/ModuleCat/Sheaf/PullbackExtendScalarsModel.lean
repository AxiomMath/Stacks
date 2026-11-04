module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Extension of scalars along a presheaf of rings whose sheafification is the target

Let `φ : S ⟶ R` be a morphism of sheaves of rings over a continuous functor of sites, let
`R₀` be a presheaf of rings together with a locally bijective morphism `α : R₀ ⟶ R` of
presheaves of rings — so `R` *is* the sheafification of `R₀` — and let `ν₀ : S ⟶ R₀` lift `φ`.
Then the extension of scalars of sheaves of modules along `φ` is computed by the **objectwise**
extension of scalars along `ν₀`, followed by the sheafification functor of
`PresheafOfModules.sheafification α`:

`pullback φ ≅ forget S ⋙ extendScalars ν₀ ⋙ sheafification α`.

Mathlib's `SheafOfModules.pullbackIso` is the case `R₀ = R` and `α = 𝟙`; the point of allowing a
genuine `R₀` is that `PresheafOfModules.sheafification α` has the same underlying abelian sheaf
as the abelian sheafification of the underlying abelian presheaf
(`PresheafOfModules.sheafificationCompToSheaf`), so the *sections* of the extension of scalars
along `φ` become the objectwise tensor products `R₀(V) ⊗_{S(V)} M(V)` up to sheafification —
even when nothing describes the sections of `R` itself. That is the situation of the Frobenius
colimit of the structure sheaf in Stacks Tag 0EXB.

## Main definitions

* `Stacks.SheafOfModules.pullbackIsoExtendScalars`: the isomorphism above.
* `Stacks.SheafOfModules.pullbackCompToSheafIso`: its underlying abelian sheaf, namely
  `pullback φ ⋙ toSheaf R ≅ forget S ⋙ extendScalars ν₀ ⋙ toPresheaf R₀ ⋙ presheafToSheaf`.

## Main results

* `Stacks.SheafOfModules.forget_map_pullbackConstruction_unit_app`: **the unit of Mathlib's
  construction of the pullback of sheaves of modules, read on presheaves of modules, is the unit
  of the composite of the two adjunctions it is built from.** This is what lets the comparison
  of left adjoints be computed: both composite adjunctions then have the same unit.
* `Stacks.SheafOfModules.unit_comp_map_pullbackIsoExtendScalars_hom_app` and
  `Stacks.SheafOfModules.forget_map_pullbackPushforwardAdjunction_unit_app`: **the isomorphism
  above carries the unit of the pullback adjunction to the unit of extension of scalars along
  `ν₀` followed by the unit of sheafification**, and the same identity read with the
  isomorphism on the other side. This is what makes the isomorphism computable at all: the
  pullback of sheaves of modules is defined by a universal property, so the only thing one can
  say about a morphism out of it is what it does to the unit.

## Implementation notes

Both functors are composites of two left adjoints, so both are left adjoint, and the proof is
`CategoryTheory.Adjunction.leftAdjointUniq` on the two composite adjunctions. The hypothesis
`hres` is exactly the statement that the two right adjoints agree; it is an equality of functors
rather than an isomorphism because in every intended instance it holds on the nose — restriction
of scalars along a composite is the composite of the restrictions, and restriction of scalars
along an identity is the identity functor — and an isomorphism would have to be transported
through `CategoryTheory.Adjunction.ofNatIsoRight` with no gain.

The site functor `F` is kept arbitrary rather than specialised to the identity. The pushforward
of sheaves of modules along the identity of a topological space is spelled
`SheafOfModules.pushforward` at `Opens.map (𝟙 X)`, which is definitionally but not syntactically
the identity functor of the opens; taking `F` as a variable and `hres` as a hypothesis lets the
consumer discharge that coincidence once, by `rfl`, instead of rewriting a functor argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ u v₂ u₂ v₃ u₃

namespace CategoryTheory

/-- **A transport of functors commutes with the image of a morphism.** This is
`CategoryTheory.Functor.congr_hom` with the two transports on opposite sides, which is the form
in which a transport is moved past the image of a morphism. -/
lemma Functor.eqToHom_comp_map {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
    {U V : C ⥤ D} (h : U = V) {X Y : C} (f : X ⟶ Y) :
    eqToHom (Functor.congr_obj h X) ≫ V.map f = U.map f ≫ eqToHom (Functor.congr_obj h Y) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **A morphism into the image of an object is recovered from its composite with the image of
an isomorphism.** -/
lemma Functor.eq_comp_map_hom_comp_map_inv {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
    [Category.{v₃} D] (U : C ⥤ D) {Z Z' : C} (i : Z ≅ Z') {W : D} (f : W ⟶ U.obj Z) :
    f = (f ≫ U.map i.hom) ≫ U.map i.inv := by
  rw [Category.assoc, ← U.map_comp, i.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

end CategoryTheory

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {F : C ⥤ C} [Functor.IsContinuous F J J]
  {S R : Sheaf J RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R)
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  (ν₀ : S.obj ⟶ R₀)
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint]

/-- The composite adjunction of Mathlib's description of the pullback of sheaves of modules:
extension of scalars of presheaves of modules along `φ`, followed by sheafification. -/
noncomputable abbrev pullbackSheafificationAdjunction :
    PresheafOfModules.pullback.{u} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) ⊣
      (_root_.SheafOfModules.forget R ⋙
          PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
        PresheafOfModules.pushforward.{u} φ.hom :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u} φ.hom).comp
    (PresheafOfModules.sheafificationAdjunction (R₀ := R.obj) (𝟙 R.obj))

/-- The composite adjunction of the objectwise description: objectwise extension of scalars
along `ν₀`, followed by the sheafification functor attached to `α`. -/
noncomputable abbrev extendScalarsSheafificationAdjunction :
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀ ⋙
        PresheafOfModules.sheafification α ⊣
      (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α) ⋙
        PresheafOfModules.restrictScalars.{u} ν₀ :=
  (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).comp
    (PresheafOfModules.sheafificationAdjunction α)

/-- **The unit of Mathlib's construction of the pullback of sheaves of modules, read on
presheaves of modules, is the unit of the composite of the two adjunctions it is built from**:
extension of scalars of presheaves of modules along `φ`, followed by sheafification.

The composite is spelled out rather than named
`Stacks.SheafOfModules.pullbackSheafificationAdjunction`, so that nothing has to be known about
the `homEquiv` of a composite adjunction; `CategoryTheory.Adjunction.comp_unit_app` turns this
statement into the named form, which is
`Stacks.SheafOfModules.forget_map_pullbackConstruction_unit_app'`. -/
lemma forget_map_pullbackConstruction_unit_app (G : _root_.SheafOfModules.{u} S) :
    (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.PullbackConstruction.adjunction.{u} φ).unit.app G) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} φ.hom).unit.app G.val ≫
        (PresheafOfModules.pushforward.{u} φ.hom).map
          ((PresheafOfModules.sheafificationAdjunction (R₀ := R.obj) (𝟙 R.obj)).unit.app
            ((PresheafOfModules.pullback.{u} φ.hom).obj G.val)) := by
  have hid : (PresheafOfModules.sheafificationAdjunction (R₀ := R.obj) (𝟙 R.obj)).unit.app
        ((PresheafOfModules.pullback.{u} φ.hom).obj G.val) ≫
      (_root_.SheafOfModules.forget R ⋙
          PresheafOfModules.restrictScalars (𝟙 R.obj)).map
        (𝟙 ((PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj
          ((PresheafOfModules.pullback.{u} φ.hom).obj G.val))) =
      (PresheafOfModules.sheafificationAdjunction (R₀ := R.obj) (𝟙 R.obj)).unit.app
        ((PresheafOfModules.pullback.{u} φ.hom).obj G.val) :=
    (congrArg (fun q ↦
        (PresheafOfModules.sheafificationAdjunction (R₀ := R.obj) (𝟙 R.obj)).unit.app
          ((PresheafOfModules.pullback.{u} φ.hom).obj G.val) ≫ q)
      (CategoryTheory.Functor.map_id (_root_.SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)) _)).trans (Category.comp_id _)
  exact congrArg (fun q ↦
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} φ.hom).unit.app G.val ≫
      (PresheafOfModules.pushforward.{u} φ.hom).map q) hid

/-- `Stacks.SheafOfModules.forget_map_pullbackConstruction_unit_app` with the composite
adjunction named. -/
lemma forget_map_pullbackConstruction_unit_app' (G : _root_.SheafOfModules.{u} S) :
    (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.PullbackConstruction.adjunction.{u} φ).unit.app G) =
      (pullbackSheafificationAdjunction φ).unit.app G.val :=
  (forget_map_pullbackConstruction_unit_app φ G).trans
    (Adjunction.comp_unit_app _ _ _).symm

variable (hres :
  (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α) ⋙
      PresheafOfModules.restrictScalars.{u} ν₀ =
    (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.pushforward.{u} φ.hom)

include hres

/-- **Extension of scalars of presheaves of modules along `ν₀`, followed by sheafification, is
extension of scalars of sheaves of modules along `φ`.** Both sides are left adjoint to the same
functor, by `hres`. -/
noncomputable def extendScalarsSheafificationIsoPullback :
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀ ⋙
        PresheafOfModules.sheafification α ≅
      PresheafOfModules.pullback.{u} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq
    ((extendScalarsSheafificationAdjunction α ν₀).ofNatIsoRight (eqToIso hres))
    (pullbackSheafificationAdjunction φ)

/-- **The pullback of sheaves of modules is the objectwise extension of scalars along `ν₀`
followed by sheafification.** -/
noncomputable def pullbackIsoExtendScalars :
    _root_.SheafOfModules.pullback.{u} φ ≅
      _root_.SheafOfModules.forget S ⋙
        Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀ ⋙
          PresheafOfModules.sheafification α :=
  _root_.SheafOfModules.pullbackIso.{u} φ ≪≫
    (Functor.isoWhiskerLeft _ (extendScalarsSheafificationIsoPullback φ α ν₀ hres)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _)

/-- **The comparison of the two descriptions of the pullback carries the unit of the pullback
adjunction to the unit of the composite objectwise adjunction.** Read through
`SheafOfModules.forget`, the unit of `SheafOfModules.pullbackPushforwardAdjunction` followed by
restriction of scalars of `Stacks.SheafOfModules.pullbackIsoExtendScalars` is the unit of
extension of scalars along `ν₀` followed by the unit of sheafification. The transport is
`hres`, which is what makes the two the units of adjunctions with one and the same right
adjoint. -/
lemma unit_comp_map_pullbackIsoExtendScalars_hom_app (G : _root_.SheafOfModules.{u} S) :
    (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) ≫
      ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
          PresheafOfModules.pushforward.{u} φ.hom).map
        ((pullbackIsoExtendScalars φ α ν₀ hres).hom.app G) =
      ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).unit.app G.val ≫
          (PresheafOfModules.restrictScalars ν₀).map
            ((PresheafOfModules.sheafificationAdjunction α).unit.app
              ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val))) ≫
        eqToHom (Functor.congr_obj hres
          ((PresheafOfModules.sheafification α).obj
            ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val))) := by
  have hi : extendScalarsSheafificationIsoPullback φ α ν₀ hres =
      Adjunction.leftAdjointUniq
        ((extendScalarsSheafificationAdjunction α ν₀).ofNatIsoRight (eqToIso hres))
        (pullbackSheafificationAdjunction φ) := rfl
  have hk : (pullbackIsoExtendScalars φ α ν₀ hres).hom.app G =
      (_root_.SheafOfModules.pullbackIso.{u} φ).hom.app G ≫
        (extendScalarsSheafificationIsoPullback φ α ν₀ hres).inv.app G.val := by
    simp only [pullbackIsoExtendScalars, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.comp_id]
    rfl
  have hB : (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map
          ((_root_.SheafOfModules.pullbackIso.{u} φ).hom.app G) =
      (_root_.SheafOfModules.PullbackConstruction.adjunction.{u} φ).unit.app G :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ G
  have hA : (pullbackSheafificationAdjunction φ).unit.app G.val ≫
        ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
            PresheafOfModules.pushforward.{u} φ.hom).map
          ((extendScalarsSheafificationIsoPullback φ α ν₀ hres).inv.app G.val) =
      ((extendScalarsSheafificationAdjunction α ν₀).ofNatIsoRight
        (eqToIso hres)).unit.app G.val := by
    rw [hi, ← Adjunction.unit_leftAdjointUniq_hom_app
      ((extendScalarsSheafificationAdjunction α ν₀).ofNatIsoRight (eqToIso hres))
      (pullbackSheafificationAdjunction φ) G.val, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have h6 : ((extendScalarsSheafificationAdjunction α ν₀).ofNatIsoRight
        (eqToIso hres)).unit.app G.val =
      ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).unit.app G.val ≫
          (PresheafOfModules.restrictScalars ν₀).map
            ((PresheafOfModules.sheafificationAdjunction α).unit.app
              ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val))) ≫
        eqToHom (Functor.congr_obj hres
          ((PresheafOfModules.sheafification α).obj
            ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val))) := by
    rw [Adjunction.ofNatIsoRight_unit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app,
      Adjunction.comp_unit_app]
  have h1 := congrArg (fun f ↦ ((_root_.SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
        PresheafOfModules.pushforward.{u} φ.hom).map f) hk
  have h4 : (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) ≫
      ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
          PresheafOfModules.pushforward.{u} φ.hom).map
        ((_root_.SheafOfModules.pullbackIso.{u} φ).hom.app G) =
      (pullbackSheafificationAdjunction φ).unit.app G.val :=
    ((CategoryTheory.Functor.map_comp (_root_.SheafOfModules.forget S)
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G)
          ((_root_.SheafOfModules.pushforward.{u} φ).map
            ((_root_.SheafOfModules.pullbackIso.{u} φ).hom.app G))).symm.trans
        (congrArg (_root_.SheafOfModules.forget S).map hB)).trans
      (forget_map_pullbackConstruction_unit_app' φ G)
  refine Eq.trans (congrArg (fun q ↦ (_root_.SheafOfModules.forget S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) ≫ q)
    (h1.trans (CategoryTheory.Functor.map_comp _ _ _))) ?_
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun q ↦ q ≫ _) h4).trans hA)).trans h6

/-- **The unit of the pullback adjunction, read on presheaves of modules, is the unit of
extension of scalars along `ν₀` followed by the sheafification comparison.** This is
`Stacks.SheafOfModules.unit_comp_map_pullbackIsoExtendScalars_hom_app` with the comparison moved
to the other side and read back through the sheafification adjunction, which is the form the
base change of the objectwise extensions of scalars is compared in. -/
lemma forget_map_pullbackPushforwardAdjunction_unit_app (G : _root_.SheafOfModules.{u} S) :
    (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) =
      ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).unit.app G.val ≫
          (PresheafOfModules.restrictScalars ν₀).map
            (PresheafOfModules.sheafificationHomEquiv α
              ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G))) ≫
        eqToHom (Functor.congr_obj hres ((_root_.SheafOfModules.pullback.{u} φ).obj G)) := by
  have hθ : PresheafOfModules.sheafificationHomEquiv α
        ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G) =
      (PresheafOfModules.sheafificationAdjunction α).unit.app
          ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val) ≫
        (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).map
          ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G) :=
    Adjunction.homEquiv_unit (PresheafOfModules.sheafificationAdjunction α) _ _
      ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G)
  have hA := unit_comp_map_pullbackIsoExtendScalars_hom_app φ α ν₀ hres G
  have hcong := Functor.eqToHom_comp_map hres
    ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G)
  refine Eq.trans (Functor.eq_comp_map_hom_comp_map_inv
    ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.pushforward.{u} φ.hom)
    ((pullbackIsoExtendScalars φ α ν₀ hres).app G)
    ((_root_.SheafOfModules.forget S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G))) ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫
    ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
        PresheafOfModules.pushforward.{u} φ.hom).map
      ((pullbackIsoExtendScalars φ α ν₀ hres).inv.app G)) hA) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun q ↦
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).unit.app G.val ≫
      (PresheafOfModules.restrictScalars ν₀).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app
          ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀).obj G.val))) ≫ q)
    hcong) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun q ↦ q ≫
    eqToHom (Functor.congr_obj hres ((_root_.SheafOfModules.pullback.{u} φ).obj G))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun q ↦
      (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν₀).unit.app G.val ≫ q)
    ((CategoryTheory.Functor.map_comp (PresheafOfModules.restrictScalars ν₀) _ _).symm.trans
      (congrArg (PresheafOfModules.restrictScalars ν₀).map hθ.symm))

/-- **The abelian sheaf underlying the pullback of a sheaf of modules**: it is the
sheafification of the abelian presheaf of the objectwise tensor products
`V ↦ R₀(V) ⊗_{S(V)} M(V)`. This is the identification Stacks Tag 0EXB needs, and the only one
available when nothing describes the sections of `R`. -/
noncomputable def pullbackCompToSheafIso :
    _root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.toSheaf R ≅
      _root_.SheafOfModules.forget S ⋙
        Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν₀ ⋙
          PresheafOfModules.toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (pullbackIsoExtendScalars φ α ν₀ hres) _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (PresheafOfModules.sheafificationCompToSheaf α) ≪≫
          (Functor.associator _ _ _).symm)

/-- **The abelian sheaf comparison is `SheafOfModules.toSheaf` of the comparison of sheaves of
modules.** The associators and `PresheafOfModules.sheafificationCompToSheaf`, which is the
identity, contribute nothing. Stating a square with the left-hand side spelled this way keeps
the target of the right-hand side in the `presheafToSheaf` form, which is what a consumer whose
sheaf of rings is a colimit needs: the two spellings are definitionally equal, but identifying
them at such a sheaf of rings is not something the kernel should be asked to do. -/
lemma pullbackCompToSheafIso_hom_app (G : _root_.SheafOfModules.{u} S) :
    (pullbackCompToSheafIso φ α ν₀ hres).hom.app G =
      (_root_.SheafOfModules.toSheaf R).map
        ((pullbackIsoExtendScalars φ α ν₀ hres).app G).hom := by
  simp only [pullbackCompToSheafIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    PresheafOfModules.sheafificationCompToSheaf, Category.comp_id, Category.id_comp]
  rfl

end Stacks.SheafOfModules

end
