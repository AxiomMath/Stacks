module

public import
  StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapGlobalSurjectivity

/-!
# The restriction of `𝒪_{X/S}` to an ambient scheme, compared with its structure sheaf

Let `g : (U, T, δ) ⟶ (U', T', δ')` be a morphism of the big crystalline site `CRIS(X/S)` of a
global crystalline situation.  Two sheaves of rings on the ambient scheme `T` are in play and
they are not the same sheaf:

* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf`, the restriction of
  `𝒪_{X/S}` to the opens of `T`, whose value over `W` is `Γ(W, ⊤)`, the global sections of the
  open subscheme `W`; and
* `AlgebraicGeometry.Scheme.ringCatSheaf`, the structure sheaf of `T`, whose value over `W` is
  `Γ(T, W)`.

They are identified by
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`.  The two
`f`-maps along `g` are likewise not the same morphism:
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap`, assembled from the
restrictions of `g` over the opens of `T'`, and `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`,
the comorphism of the morphism of schemes `T ⟶ T'`.

The square they form commutes. Consequently `AlgebraicGeometry.Scheme.Modules.pushforward` and
`AlgebraicGeometry.Scheme.Modules.pullback` along `T ⟶ T'` agree, up to these identifications,
with `SheafOfModules.pushforward` and `SheafOfModules.pullback` along the crystalline `f`-map of
[Stacks, Tag 07IQ].

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso_fmap` —
  **the square commutes**: conjugating the crystalline `f`-map of the restricted structure
  sheaves by the identifications with the structure sheaves of the ambient schemes gives the
  comorphism of the morphism of ambient schemes.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso` — **the two
  pushforwards agree**.  Pushing a sheaf of modules forward along the crystalline `f`-map and
  then reading its scalars in the structure sheaf of `T'` is the same as reading the scalars in
  the structure sheaf of `T` first and pushing forward along the morphism of schemes.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` — **the two
  pullbacks agree**.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe v₁ u₁ u

noncomputable section

namespace Stacks.SheafOfModules

/-- **Restriction of scalars along an isomorphism of sheaves of rings is left adjoint to
restriction of scalars along its inverse.** -/
def restrictScalarsAdjunctionOfIso {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (e : R ≅ R') :
    _root_.SheafOfModules.restrictScalars.{u} e.hom ⊣
      _root_.SheafOfModules.restrictScalars.{u} e.inv :=
  _root_.SheafOfModules.pushforwardPushforwardAdj (Adjunction.id (C := C)) e.hom e.inv
    (by
      ext U x
      change (RingCat.Hom.hom (R'.obj.map (𝟙 U))) x =
        (RingCat.Hom.hom (e.inv.hom.app U ≫ e.hom.hom.app U)) x
      rw [R'.obj.map_id]
      exact congrArg (fun φ : R'.obj.obj U ⟶ R'.obj.obj U ↦ (RingCat.Hom.hom φ) x)
        (congrArg (fun k ↦ k.hom.app U) e.inv_hom_id).symm)
    (by
      ext U x
      change (RingCat.Hom.hom (e.inv.hom.app U ≫ R.obj.map (𝟙 U)))
          ((RingCat.Hom.hom (e.hom.hom.app U)) x) = x
      rw [R.obj.map_id, Category.comp_id]
      exact congrArg (fun φ : R.obj.obj U ⟶ R.obj.obj U ↦ (RingCat.Hom.hom φ) x)
        (congrArg (fun k ↦ k.hom.app U) e.hom_inv_id))

end Stacks.SheafOfModules

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}

/-! ### The commuting square of sheaves of rings -/

/-- **The crystalline `f`-map of the restricted structure sheaves is the comorphism of the
morphism of ambient schemes**, conjugated by the identification of the restriction of `𝒪_{X/S}`
with the structure sheaf of the ambient scheme. -/
theorem ringRestrictionSheafStructureIso_fmap (g : A ⟶ B) :
    ringRestrictionSheafFMap g ≫
        ((Opens.map g.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology ↥B.thickening.target.scheme)
            (Opens.grothendieckTopology ↥A.thickening.target.scheme)).map
          (ringRestrictionSheafStructureIso A).hom =
      (ringRestrictionSheafStructureIso B).hom ≫ g.targetHom.hom.toRingCatSheafHom := by
  apply Sheaf.hom_ext
  ext W : 2
  change (forget₂ CommRingCat.{u} RingCat.{u}).map
      ((restrictOpenMap g W.unop).targetHom.hom.appTop ≫
        (Scheme.Opens.topIso (g.targetHom.hom ⁻¹ᵁ W.unop)).hom) =
    (forget₂ CommRingCat.{u} RingCat.{u}).map
      ((Scheme.Opens.topIso W.unop).hom ≫ g.targetHom.hom.app W.unop)
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    ((congrArg
        (fun k ↦ Scheme.Hom.appTop k ≫
          (Scheme.Opens.topIso (g.targetHom.hom ⁻¹ᵁ W.unop)).hom)
        (restrictOpenMap_targetHom g W.unop)).trans
      (morphismRestrict_appTop_topIso g.targetHom.hom W.unop))

/-- **The commuting square of
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso_fmap`, with
the identifications run in the other direction.**  The crystalline `f`-map, read from the
structure sheaf of `T'`, is the comorphism of the morphism of ambient schemes followed by the
identification over `T`. -/
theorem ringRestrictionSheafStructureIso_inv_fmap (g : A ⟶ B) :
    (ringRestrictionSheafStructureIso B).inv ≫ ringRestrictionSheafFMap g =
      g.targetHom.hom.toRingCatSheafHom ≫
        ((Opens.map g.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology ↥B.thickening.target.scheme)
            (Opens.grothendieckTopology ↥A.thickening.target.scheme)).map
          (ringRestrictionSheafStructureIso A).inv := by
  refine (Iso.inv_comp_eq _).2 ?_
  erw [← Category.assoc, ← ringRestrictionSheafStructureIso_fmap, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id]
  simp

/-! ### The two pushforwards -/

/-- **The pushforward along the crystalline `f`-map is the pushforward along the morphism of
ambient schemes.**  Pushing a sheaf of modules on the ambient scheme `T` forward along the
`f`-map of [Stacks, Tag 07IQ] and then reading its scalars in the structure sheaf of `T'` is the
same as reading the scalars in the structure sheaf of `T` first and pushing forward along the
morphism of schemes `T ⟶ T'`. -/
def ambientSchemePushforwardIso (g : A ⟶ B) :
    SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g) ⋙
        SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso B).inv ≅
      SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso A).inv ⋙
        Scheme.Modules.pushforward g.targetHom.hom := by
  change SheafOfModules.pushforward.{u}
      ((ringRestrictionSheafStructureIso B).inv ≫ ringRestrictionSheafFMap g) ≅
    SheafOfModules.pushforward.{u}
      (g.targetHom.hom.toRingCatSheafHom ≫
        ((Opens.map g.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥B.thickening.target.scheme)
          (Opens.grothendieckTopology ↥A.thickening.target.scheme)).map
        (ringRestrictionSheafStructureIso A).inv)
  exact SheafOfModules.pushforwardCongr (ringRestrictionSheafStructureIso_inv_fmap g)

/-- **The comparison of the two pushforwards is the identity on sections.** -/
theorem ambientSchemePushforwardIso_hom_app_val_app (g : A ⟶ B)
    (N : SheafOfModules.{u} A.ringRestrictionSheaf)
    (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (x : N.val.obj (op (g.targetHom.hom ⁻¹ᵁ W.unop))) :
    ((ambientSchemePushforwardIso g).hom.app N).val.app W x = x := rfl

/-! ### The two pullbacks -/

/-- **The pullback along the crystalline `f`-map is the pullback along the morphism of ambient
schemes.**  Reading the scalars of a sheaf of modules on `T'` in the restriction of `𝒪_{X/S}`
and pulling back along the `f`-map of [Stacks, Tag 07IQ] is the same as pulling back along the
morphism of schemes `T ⟶ T'` and reading the scalars in the restriction of `𝒪_{X/S}` afterwards. -/
def ambientSchemePullbackIso (g : A ⟶ B) :
    SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso B).hom ⋙
        SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g) ≅
      Scheme.Modules.pullback g.targetHom.hom ⋙
        SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso A).hom :=
  Adjunction.leftAdjointUniq
    ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (ringRestrictionSheafStructureIso B)).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)))
    (((Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom).comp
        (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
          (ringRestrictionSheafStructureIso A))).ofNatIsoRight
      (ambientSchemePushforwardIso g).symm)

end Thickening

end Crystalline.GlobalCrystallineSituation

end

end
