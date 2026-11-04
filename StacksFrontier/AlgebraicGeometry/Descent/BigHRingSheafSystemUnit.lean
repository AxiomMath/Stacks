module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystem

/-!
# Pushforward and the unit of extension of scalars for a system of sheaves of rings

For a system of sheaves of rings `𝓡` on the big h category over `S`
(`AlgebraicGeometry.BigHOver.RingSheafSystem`) and an arrow `f : V ⟶ U`, extension of scalars
along `𝓡.hom f` is left adjoint to pushforward along it. This file records the two facts about
these adjunctions that a Zariski gluing argument needs, at an arbitrary system:

* pushforwards along a commuting triangle of arrows compose, by an isomorphism which is the
  identity on sections up to a restriction along an equality of opens
  (`AlgebraicGeometry.BigHOver.RingSheafSystem.pushTriangle`);
* the unit of extension of scalars along a composite is the composite of the units, read through
  the composition comparison of the pseudofunctor of modules
  (`AlgebraicGeometry.BigHOver.RingSheafSystem.unit_comp_push_map_mapComp'_hom`).

## Main definitions

* `AlgebraicGeometry.BigHOver.RingSheafSystem.push`: pushforward of sheaves of modules along an
  arrow.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.adj`: the adjunction between extension of scalars
  and pushforward along an arrow.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.pushCongr` and
  `AlgebraicGeometry.BigHOver.RingSheafSystem.pushTriangle`: pushforward along equal arrows, and
  along a commuting triangle.

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.pushTriangle_hom_app_val_app`: the triangle
  comparison on sections.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.unit_comp_push_map_mapComp'_hom`: the unit along a
  composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (𝓡 : RingSheafSystem B S hS)

/-- **Pushforward of sheaves of modules along an arrow** of the big h category over `S`. -/
abbrev push {V U : BigHOver B S hS} (f : V ⟶ U) :
    SheafOfModules.{u} (𝓡.ring V) ⥤ SheafOfModules.{u} (𝓡.ring U) :=
  SheafOfModules.pushforward.{u} (𝓡.hom f)

/-- **Extension of scalars is left adjoint to pushforward**, along an arrow. -/
abbrev adj {V U : BigHOver B S hS} (f : V ⟶ U) : 𝓡.pull f.op ⊣ 𝓡.push f :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (𝓡.hom f)

/-- The transition functor of the pseudofunctor of modules along an arrow is extension of
scalars. -/
lemma modulePseudofunctor_map {V U : BigHOver B S hS} (f : V ⟶ U) :
    (𝓡.modulePseudofunctor.map f.op.toLoc).toFunctor = 𝓡.pull f.op :=
  rfl

/-- Pushforward along two equal arrows. -/
def pushCongr {V U : BigHOver B S hS} {f g : V ⟶ U} (h : f = g) : 𝓡.push f ≅ 𝓡.push g :=
  eqToIso (congrArg (fun m : V ⟶ U => 𝓡.push m) h)

/-- Pushforward along two equal arrows, on sections: the restriction along the equality of the
two preimages. -/
lemma pushCongr_hom_app_val_app {V U : BigHOver B S hS} {f g : V ⟶ U} (h : f = g)
    (X : SheafOfModules.{u} (𝓡.ring V)) (T : (((toScheme B S hS).obj U).Opens))
    (x : ToType (((𝓡.push f).obj X).val.obj (op T))) :
    ((𝓡.pushCongr h).hom.app X).val.app (op T) x =
      X.val.map (eqToHom (by rw [h])).op x := by
  subst h
  simp only [pushCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToHom_refl, op_id]
  exact (PresheafOfModules.map_id_apply _ _ _).symm

/-- Pushing forward along `b` and then along `a` is pushing forward along `b ≫ a`, as an
equality of functors with the sheaf of rings of the composite spelled through `hom_comp`. -/
lemma pushforward_comp_eq {Y X U : BigHOver B S hS} (b : Y ⟶ X) (a : X ⟶ U) :
    SheafOfModules.pushforward.{u} (F := Opens.map ((toScheme B S hS).map a).base ⋙
        Opens.map ((toScheme B S hS).map b).base)
      (𝓡.hom a ≫ (((toScheme B S hS).map a).ringSheafPushforward).map (𝓡.hom b)) =
    𝓡.push (b ≫ a) :=
  (rfl : SheafOfModules.pushforward.{u} (F := Opens.map ((toScheme B S hS).map a).base ⋙
        Opens.map ((toScheme B S hS).map b).base)
      (𝓡.hom a ≫ (((toScheme B S hS).map a).ringSheafPushforward).map (𝓡.hom b)) =
    SheafOfModules.pushforward.{u} (F := Opens.map ((toScheme B S hS).map (b ≫ a)).base)
      (𝓡.hom a ≫ (((toScheme B S hS).map a).ringSheafPushforward).map (𝓡.hom b))).trans
    (congrArg (fun φ => SheafOfModules.pushforward.{u} φ) (𝓡.hom_comp b a).symm)

/-- **Pushforward along a commuting triangle of arrows.** For `b ≫ a = q`, pushing forward along
`b` and then along `a` is pushing forward along `q`. -/
def pushTriangle {Y X U : BigHOver B S hS} (b : Y ⟶ X) (a : X ⟶ U) (q : Y ⟶ U)
    (h : b ≫ a = q) : 𝓡.push b ⋙ 𝓡.push a ≅ 𝓡.push q :=
  SheafOfModules.pushforwardComp.{u} (𝓡.hom a) (𝓡.hom b) ≪≫
    SheafOfModules.pushforwardCongr.{u} (F := Opens.map ((toScheme B S hS).map (b ≫ a)).base)
      (𝓡.hom_comp b a).symm ≪≫ 𝓡.pushCongr h

/-- The composition comparison of the pseudofunctor of modules at a commuting triangle
`b ≫ a = q`, at an object, typed through the transition functors. -/
def compHom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U) (hq : b ≫ a = q)
    (M : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.pull q.op).obj M ⟶ (𝓡.pull b.op).obj ((𝓡.pull a.op).obj M) :=
  (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).hom.toNatTrans.app M

/-- The inverse of `AlgebraicGeometry.BigHOver.RingSheafSystem.compHom`. -/
def compInv {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U) (hq : b ≫ a = q)
    (M : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.pull b.op).obj ((𝓡.pull a.op).obj M) ⟶ (𝓡.pull q.op).obj M :=
  (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).inv.toNatTrans.app M

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.compHom` followed by
`AlgebraicGeometry.BigHOver.RingSheafSystem.compInv` is the identity. -/
@[reassoc (attr := simp)]
lemma compHom_compInv {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U)
    (hq : b ≫ a = q) (M : SheafOfModules.{u} (𝓡.ring U)) :
    𝓡.compHom a b q hq M ≫ 𝓡.compInv a b q hq M = 𝟙 _ :=
  Cat.Hom.hom_inv_id_toNatTrans_app (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc
    q.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])) M

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.compInv` followed by
`AlgebraicGeometry.BigHOver.RingSheafSystem.compHom` is the identity. -/
@[reassoc (attr := simp)]
lemma compInv_compHom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U)
    (hq : b ≫ a = q) (M : SheafOfModules.{u} (𝓡.ring U)) :
    𝓡.compInv a b q hq M ≫ 𝓡.compHom a b q hq M = 𝟙 _ :=
  Cat.Hom.inv_hom_id_toNatTrans_app (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc
    q.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])) M

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.compHom` unfolded. -/
lemma mapComp'_hom_app_eq_compHom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (h : a.op.toLoc ≫ b.op.toLoc = q.op.toLoc) (hq : b ≫ a = q)
    (M : 𝓡.modulePseudofunctor.obj ⟨op U⟩) :
    (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc h).hom.toNatTrans.app M =
      𝓡.compHom a b q hq M :=
  rfl

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.compInv` unfolded. -/
lemma mapComp'_inv_app_eq_compInv {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (h : a.op.toLoc ≫ b.op.toLoc = q.op.toLoc) (hq : b ≫ a = q)
    (M : 𝓡.modulePseudofunctor.obj ⟨op U⟩) :
    (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc h).inv.toNatTrans.app M =
      𝓡.compInv a b q hq M :=
  rfl

/-- The transition functor of the pseudofunctor of modules on a morphism. -/
lemma modulePseudofunctor_map_map {V U : BigHOver B S hS} (f : V ⟶ U)
    {M N : 𝓡.modulePseudofunctor.obj ⟨op U⟩} (φ : M ⟶ N) :
    (𝓡.modulePseudofunctor.map f.op.toLoc).toFunctor.map φ = (𝓡.pull f.op).map φ :=
  rfl

/-- Composition in a fibre of the pseudofunctor of modules is composition of morphisms of
sheaves of modules. -/
lemma modulePseudofunctor_comp {X : BigHOver B S hS} {M N P : 𝓡.modulePseudofunctor.obj ⟨op X⟩}
    (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ g = @CategoryStruct.comp (SheafOfModules.{u} (𝓡.ring X)) _ M N P f g :=
  rfl

/-- Mathlib's `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` for the pseudofunctor
of modules of a system of sheaves of rings, through the composition comparisons. -/
theorem pullHom_eq_compHom {Y' Y X₁ X₂ : BigHOver B S hS} (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (r : Y' ⟶ Y)
    (b₁ : Y' ⟶ X₁) (b₂ : Y' ⟶ X₂) (h₁ : r ≫ a₁ = b₁) (h₂ : r ≫ a₂ = b₂)
    {M₁ : 𝓡.modulePseudofunctor.obj ⟨op X₁⟩} {M₂ : 𝓡.modulePseudofunctor.obj ⟨op X₂⟩}
    (φ : (𝓡.modulePseudofunctor.map a₁.op.toLoc).toFunctor.obj M₁ ⟶
      (𝓡.modulePseudofunctor.map a₂.op.toLoc).toFunctor.obj M₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ r b₁ b₂ h₁ h₂ =
      𝓡.compHom a₁ r b₁ h₁ M₁ ≫ (𝓡.pull r.op).map φ ≫ 𝓡.compInv a₂ r b₂ h₂ M₂ := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [mapComp'_hom_app_eq_compHom _ _ _ _ _ h₁, mapComp'_inv_app_eq_compInv _ _ _ _ _ h₂,
    modulePseudofunctor_map_map]
  rfl

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.pullHom_eq_compHom` for a morphism typed through
the transition functors. -/
theorem pullHom_eq_compHom' {Y' Y X₁ X₂ : BigHOver B S hS} (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)
    (r : Y' ⟶ Y) (b₁ : Y' ⟶ X₁) (b₂ : Y' ⟶ X₂) (h₁ : r ≫ a₁ = b₁) (h₂ : r ≫ a₂ = b₂)
    {M₁ : SheafOfModules.{u} (𝓡.ring X₁)} {M₂ : SheafOfModules.{u} (𝓡.ring X₂)}
    (φ : (𝓡.pull a₁.op).obj M₁ ⟶ (𝓡.pull a₂.op).obj M₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := 𝓡.modulePseudofunctor)
        (M₁ := M₁) (M₂ := M₂) (f₁ := a₁) (f₂ := a₂) φ r b₁ b₂ h₁ h₂ =
      𝓡.compHom a₁ r b₁ h₁ M₁ ≫ (𝓡.pull r.op).map φ ≫ 𝓡.compInv a₂ r b₂ h₂ M₂ :=
  𝓡.pullHom_eq_compHom a₁ a₂ r b₁ b₂ h₁ h₂ φ

/-- A morphism that is the transport `pullHom` of a morphism `φ` along `r` is the conjugate of the
extension of scalars of `φ` along `r` by the composition comparisons. Stated with both morphisms
typed through the transition functors. -/
theorem eq_compHom_of_pullHom_eq {Y' Y X₁ X₂ : BigHOver B S hS} (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)
    (r : Y' ⟶ Y) (b₁ : Y' ⟶ X₁) (b₂ : Y' ⟶ X₂) (h₁ : r ≫ a₁ = b₁) (h₂ : r ≫ a₂ = b₂)
    {M₁ : SheafOfModules.{u} (𝓡.ring X₁)} {M₂ : SheafOfModules.{u} (𝓡.ring X₂)}
    (φ : (𝓡.pull a₁.op).obj M₁ ⟶ (𝓡.pull a₂.op).obj M₂)
    (ψ : (𝓡.pull b₁.op).obj M₁ ⟶ (𝓡.pull b₂.op).obj M₂)
    (h : Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := 𝓡.modulePseudofunctor)
        (M₁ := M₁) (M₂ := M₂) (f₁ := a₁) (f₂ := a₂) φ r b₁ b₂ h₁ h₂ = ψ) :
    ψ = 𝓡.compHom a₁ r b₁ h₁ M₁ ≫ (𝓡.pull r.op).map φ ≫ 𝓡.compInv a₂ r b₂ h₂ M₂ := by
  rw [← h]
  exact 𝓡.pullHom_eq_compHom a₁ a₂ r b₁ b₂ h₁ h₂ φ

/-- Naturality of `AlgebraicGeometry.BigHOver.RingSheafSystem.compHom` in the sheaf of modules. -/
lemma compHom_naturality {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U)
    (hq : b ≫ a = q) {M M' : SheafOfModules.{u} (𝓡.ring U)} (f : M ⟶ M') :
    (𝓡.pull q.op).map f ≫ 𝓡.compHom a b q hq M' =
      𝓡.compHom a b q hq M ≫ (𝓡.pull b.op).map ((𝓡.pull a.op).map f) :=
  (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).hom.toNatTrans.naturality f

/-- The composition comparison of the pseudofunctor of modules at a commuting triangle, at an
object: the inverse of the comparison of extension of scalars of
`AlgebraicGeometry.Scheme.ringPullbackCompOfEq`, transported along the triangle. -/
lemma mapComp'_hom_app_eq {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U)
    (hq : b ≫ a = q) (M : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).hom.toNatTrans.app M =
      eqToHom (by rw [← hq]; rfl) ≫ (𝓡.pullComp a.op b.op).inv.app M := by
  subst hq
  rfl

/-- The composition comparison of the pseudofunctor of modules at a literal composite. -/
lemma mapComp'_hom_app_rfl {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (M : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.modulePseudofunctor.mapComp' a.op.toLoc b.op.toLoc (b ≫ a).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M =
      (𝓡.pullComp a.op b.op).inv.app M :=
  (𝓡.mapComp'_hom_app_eq a b (b ≫ a) rfl M).trans (Category.id_comp _)

/-- **The unit of extension of scalars along a composite, at the literal composite of sheaves
of rings.** This is Mathlib's `CategoryTheory.SheafOfModules.pullbackComp` read through units:
the unit along `φ ≫ F_* ψ`, followed by pushforward of the comparison, is the unit along `φ`
followed by pushforward of the unit along `ψ`. -/
lemma unit_comp_pullbackComp_inv {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {D' : Type u} [Category.{u} D'] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'} {F : C ⥤ D} {G : D ⥤ D'} [F.IsContinuous J K]
    [G.IsContinuous K K'] [(F ⋙ G).IsContinuous J K']
    {R₀ : Sheaf J RingCat.{u}} {R₁ : Sheaf K RingCat.{u}} {R₂ : Sheaf K' RingCat.{u}}
    (φ : R₀ ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R₁)
    (ψ : R₁ ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R₂)
    (M : SheafOfModules.{u} R₀) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).unit.app M ≫
        (SheafOfModules.pushforward.{u} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).map
          ((SheafOfModules.pullbackComp.{u} φ ψ).inv.app M) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app M ≫
        (SheafOfModules.pushforward.{u} φ).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u} ψ).unit.app
            ((SheafOfModules.pullback.{u} φ).obj M)) := by
  have h := unit_conjugateEquiv
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} ψ))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (SheafOfModules.pullbackComp.{u} φ ψ).inv M
  rw [SheafOfModules.pullbackComp, Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Adjunction.comp_unit_app] at h
  exact h.symm.trans (Category.comp_id _)

/-- `CategoryTheory.SheafOfModules.pushforwardCongr` at a reflexivity proof is the identity. -/
lemma pushforwardCongr_refl {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
    {R₀ : Sheaf J RingCat.{u}} {R₁ : Sheaf K RingCat.{u}}
    (φ : R₀ ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R₁) :
    SheafOfModules.pushforwardCongr.{u} (rfl : φ = φ) = Iso.refl _ := by
  ext : 2
  rfl

/-- **The unit of extension of scalars along a composite**, with the sheaf of rings of the
composite given by an equation: the unit along `c`, followed by pushforward of the comparison
`AlgebraicGeometry.Scheme.ringPullbackCompOfEq`, is the unit along `a` followed by pushforward
of the unit along `b`. -/
lemma unit_comp_ringPullbackCompOfEq_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    {RZ : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u}}
    (a : RZ ⟶ (g.ringSheafPushforward).obj RY) (b : RY ⟶ (f.ringSheafPushforward).obj RX)
    (c : RZ ⟶ ((f ≫ g).ringSheafPushforward).obj RX)
    (hc : c = a ≫ (g.ringSheafPushforward).map b) (M : SheafOfModules.{u} RZ) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} c).unit.app M ≫
        (SheafOfModules.pushforward.{u} c).map
          ((Scheme.ringPullbackCompOfEq f g a b c hc).inv.app M) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} a).unit.app M ≫
        (SheafOfModules.pushforward.{u} a).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u} b).unit.app
            ((SheafOfModules.pullback.{u} a).obj M)) ≫
        (SheafOfModules.pushforwardCongr.{u} (F := Opens.map (f ≫ g).base) hc.symm).hom.app _ := by
  subst hc
  simp only [Scheme.ringPullbackCompOfEq_self]
  exact unit_comp_pullbackComp_inv a b M

/-- At the literal composite, the triangle comparison is Mathlib's comparison of pushforwards
along equal morphisms of sheaves of rings. -/
lemma pushTriangle_rfl_hom_app {Y X U : BigHOver B S hS} (b : Y ⟶ X) (a : X ⟶ U)
    (Z : SheafOfModules.{u} (𝓡.ring Y)) :
    (𝓡.pushTriangle b a (b ≫ a) rfl).hom.app Z =
      (SheafOfModules.pushforwardCongr.{u}
        (F := Opens.map ((toScheme B S hS).map (b ≫ a)).base)
        (𝓡.hom_comp b a).symm).hom.app Z := by
  simp only [pushTriangle, pushCongr, eqToIso_refl, Iso.trans_hom, NatTrans.comp_app]
  exact Category.id_comp _

/-- **The unit along a commuting triangle.** For `b ≫ a = q`, the unit of extension of scalars
along `q`, followed by pushforward of the composition comparison of the pseudofunctor of
modules, is the unit along `a` followed by pushforward of the unit along `b`, read through the
triangle comparison of pushforwards. -/
lemma unit_comp_push_map_mapComp'_hom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (hq : b ≫ a = q) (M : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.adj q).unit.app M ≫ (𝓡.push q).map (𝓡.compHom a b q hq M) =
      (𝓡.adj a).unit.app M ≫ (𝓡.push a).map ((𝓡.adj b).unit.app ((𝓡.pull a.op).obj M)) ≫
        (𝓡.pushTriangle b a q hq).hom.app _ := by
  subst hq
  rw [pushTriangle_rfl_hom_app, compHom, mapComp'_hom_app_rfl]
  exact unit_comp_ringPullbackCompOfEq_inv ((toScheme B S hS).map b)
    ((toScheme B S hS).map a) (𝓡.hom a) (𝓡.hom b) (𝓡.hom (b ≫ a)) (𝓡.hom_comp b a) M

/-- **Transposition along a commuting triangle.** For `b ≫ a = q`, the transpose along `q` of
the composite of the composition comparison of the pseudofunctor of modules, of the extension of
scalars along `b` of a morphism `β`, and of a morphism `γ`, is the transpose of `β` along `a`
followed by pushforward along `a` of the transpose of `γ` along `b`, read through the triangle
comparison of pushforwards. -/
lemma homEquiv_mapComp'_hom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (hq : b ≫ a = q) {M : SheafOfModules.{u} (𝓡.ring U)}
    {D : SheafOfModules.{u} (𝓡.ring X)} {E : SheafOfModules.{u} (𝓡.ring Y)}
    (β : (𝓡.pull a.op).obj M ⟶ D) (γ : (𝓡.pull b.op).obj D ⟶ E) :
    (𝓡.adj q).homEquiv M E (𝓡.compHom a b q hq M ≫ (𝓡.pull b.op).map β ≫ γ) =
      (𝓡.adj a).homEquiv M D β ≫ (𝓡.push a).map ((𝓡.adj b).homEquiv D E γ) ≫
        (𝓡.pushTriangle b a q hq).hom.app E := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, 𝓡.unit_comp_push_map_mapComp'_hom a b q hq M,
    Category.assoc, Category.assoc, ← (𝓡.pushTriangle b a q hq).hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc]
  congr 3
  have hn := (𝓡.adj b).unit.naturality β
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, ← reassoc_of% hn]

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
