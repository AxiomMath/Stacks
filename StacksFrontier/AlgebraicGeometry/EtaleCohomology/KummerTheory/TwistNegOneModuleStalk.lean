module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModulePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneTransition

/-!
# The stalks of the Tate twist `𝓗om(μ_N, G)`

Let `Φ` be a point of the small étale site of `X` (for instance the point
`AlgebraicGeometry.Scheme.pointSmallEtale x̄` of a geometric point). A section `α` of
`G(-1) = 𝓗om(μ_N, G)` and a section `s` of `μ_N` over the same étale neighbourhood pair to the
section `α(s)` of `G`, naturally in the neighbourhood
(`Stacks.Kummer.twistNegOneModulePairing_naturality`). Passing to germs gives a pairing of stalks
`G(-1)_Φ × (μ_N)_Φ → G_Φ` (`Stacks.Kummer.fiberPairing`, for any natural pairing of presheaves).
When `e` is the germ of a primitive `N`-th root of unity `ζ` on a neighbourhood carrying one,
`a ↦ ⟨a, e⟩` is a bijection `G(-1)_Φ ≃ G_Φ`
(`Stacks.Kummer.bijective_twistNegOneFiberPairing_root`): on every refinement of that
neighbourhood, evaluation at `ζ` is bijective
(`Stacks.Kummer.bijective_twistNegOneModuleEvalRoot`). The pairing commutes with the maps of stalks
induced by morphisms of points (`Stacks.Kummer.fiberPairing_presheafFiber_hom`).

## Main definitions

* `Stacks.Kummer.fiberPairing`: the pairing of stalks induced by a natural pairing of presheaves.

## Main results

* `Stacks.Kummer.fiberPairing_germ`: on germs at a common neighbourhood it is the pairing of
  sections.
* `Stacks.Kummer.bijective_fiberPairing_of_bijective`: pairing against the germ of a section `r`
  is bijective once pairing against the restrictions of `r` is bijective on sections.
* `Stacks.Kummer.bijective_twistNegOneFiberPairing_root`: `G(-1)_Φ ≃ G_Φ`, `a ↦ ⟨a, ζ⟩`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GrothendieckTopology

universe w u

namespace Stacks.Kummer

/-- The forgetful functor of `ModuleCat.{u + 1} R` preserves filtered colimits of size
`w ≤ u + 1`. -/
theorem preservesFilteredColimitsOfSize_forget_moduleCat (R : Type) [Ring R] [UnivLE.{w, u + 1}] :
    PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{u + 1} R)) :=
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1} R)) :=
    comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat)
      (forget AddCommGrpCat)
  preservesFilteredColimitsOfSize_of_univLE _

variable {X : Scheme.{u}} (Φ : Point.{w} X.smallEtaleTopology) [UnivLE.{w, u + 1}]
  [LocallySmall.{w} X.Etale]

attribute [local instance] preservesFilteredColimitsOfSize_forget_moduleCat

section Germs

variable {R : Type} [Ring R] (P : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R)

omit [UnivLE.{w, u + 1}] [LocallySmall.{w} X.Etale] in
/-- Two points of the fibre are dominated by a common one. -/
theorem exists_fiber_cone {U U' : X.Etale} (u : Φ.fiber.obj U) (u' : Φ.fiber.obj U') :
    ∃ (W : X.Etale) (w : Φ.fiber.obj W) (g : W ⟶ U) (g' : W ⟶ U'),
      Φ.fiber.map g w = u ∧ Φ.fiber.map g' w = u' := by
  obtain ⟨W, f, f', -⟩ := @IsCofilteredOrEmpty.cone_objs Φ.fiber.Elements _ _
    (Φ.fiber.elementsMk U u) (Φ.fiber.elementsMk U' u')
  exact ⟨W.obj, W.val, f.hom, f'.hom, f.map_val, f'.map_val⟩

omit [LocallySmall.{w} X.Etale] in
/-- The germ of a section at the image of a point is the germ of its restriction. -/
theorem toPresheafFiber_fiber_map {U V : X.Etale} (g : V ⟶ U) (v : Φ.fiber.obj V)
    (z : ToType (P.obj (op U))) :
    Φ.toPresheafFiber U (Φ.fiber.map g v) P z = Φ.toPresheafFiber V v P (P.map g.op z) := by
  rw [Φ.toPresheafFiber_w_apply]

variable {Φ} in
omit [LocallySmall.{w} X.Etale] in
/-- The map of stalks induced by a morphism of points sends the germ at `u` to the germ at the
image of `u`. -/
theorem presheafFiber_hom_app_germ {Ψ : Point.{w} X.smallEtaleTopology} (f : Ψ ⟶ Φ) {U : X.Etale}
    (u : Φ.fiber.obj U) (z : ToType (P.obj (op U))) :
    (Point.Hom.presheafFiber f).app P (Φ.toPresheafFiber U u P z) =
      Ψ.toPresheafFiber U (f.hom.app U u) P z :=
  ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberDesc _ _ U u) z

end Germs

section Pairing

variable {R₁ R₂ R₃ : Type} [Ring R₁] [Ring R₂] [Ring R₃]
  {P₁ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₁} {P₂ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₂}
  {P₃ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₃}
  (pair : ∀ U : X.Etale, ToType (P₁.obj (op U)) → ToType (P₂.obj (op U)) → ToType (P₃.obj (op U)))
  (hpair : ∀ {U V : X.Etale} (g : V ⟶ U) (z : ToType (P₁.obj (op U))) (s : ToType (P₂.obj (op U))),
    pair V (P₁.map g.op z) (P₂.map g.op s) = P₃.map g.op (pair U z s))

/-- Two elements of stalks are germs of sections over a common neighbourhood. -/
theorem exists_germ₂ (a : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) :
    ∃ c : (U : X.Etale) × Φ.fiber.obj U × ToType (P₁.obj (op U)) × ToType (P₂.obj (op U)),
      Φ.toPresheafFiber c.1 c.2.1 P₁ c.2.2.1 = a ∧ Φ.toPresheafFiber c.1 c.2.1 P₂ c.2.2.2 = m := by
  obtain ⟨U, u, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective a
  obtain ⟨U', u', s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective m
  obtain ⟨W, w, g, g', rfl, rfl⟩ := exists_fiber_cone Φ u u'
  exact ⟨⟨W, w, P₁.map g.op z, P₂.map g'.op s⟩, (toPresheafFiber_fiber_map Φ P₁ g w z).symm,
    (toPresheafFiber_fiber_map Φ P₂ g' w s).symm⟩

include hpair in
/-- On a common neighbourhood, the germ of the pairing depends only on the germs. -/
theorem toPresheafFiber_pair_eq {U : X.Etale} (u : Φ.fiber.obj U) {z z' : ToType (P₁.obj (op U))}
    {s s' : ToType (P₂.obj (op U))} (hz : Φ.toPresheafFiber U u P₁ z = Φ.toPresheafFiber U u P₁ z')
    (hs : Φ.toPresheafFiber U u P₂ s = Φ.toPresheafFiber U u P₂ s') :
    Φ.toPresheafFiber U u P₃ (pair U z s) = Φ.toPresheafFiber U u P₃ (pair U z' s') := by
  obtain ⟨Y, f, y, rfl, hf⟩ := (Φ.toPresheafFiber_eq_iff' U u z z').1 hz
  simp only [toPresheafFiber_fiber_map] at hs
  obtain ⟨Y', f', y', rfl, hf'⟩ := (Φ.toPresheafFiber_eq_iff' Y _ _ _).1 hs
  simp only [toPresheafFiber_fiber_map, ← hpair, hf, hf']

include hpair in
/-- The germ of the pairing depends only on the germs, at any two neighbourhoods. -/
theorem toPresheafFiber_pair_eq' {U U' : X.Etale} (u : Φ.fiber.obj U) (u' : Φ.fiber.obj U')
    {z : ToType (P₁.obj (op U))} {s : ToType (P₂.obj (op U))} {z' : ToType (P₁.obj (op U'))}
    {s' : ToType (P₂.obj (op U'))}
    (hz : Φ.toPresheafFiber U u P₁ z = Φ.toPresheafFiber U' u' P₁ z')
    (hs : Φ.toPresheafFiber U u P₂ s = Φ.toPresheafFiber U' u' P₂ s') :
    Φ.toPresheafFiber U u P₃ (pair U z s) = Φ.toPresheafFiber U' u' P₃ (pair U' z' s') := by
  obtain ⟨W, w, g, g', rfl, rfl⟩ := exists_fiber_cone Φ u u'
  simp only [toPresheafFiber_fiber_map] at hz hs ⊢
  rw [← hpair, ← hpair]
  exact toPresheafFiber_pair_eq Φ pair hpair w hz hs

/-- **The pairing of stalks** induced by a natural pairing of presheaves: the germ of the pairing
of sections representing the two germs over a common neighbourhood. -/
def fiberPairing (a : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) :
    ToType (Φ.presheafFiber.obj P₃) :=
  Φ.toPresheafFiber (exists_germ₂ Φ a m).choose.1 (exists_germ₂ Φ a m).choose.2.1 P₃
    (pair _ (exists_germ₂ Φ a m).choose.2.2.1 (exists_germ₂ Φ a m).choose.2.2.2)

include hpair in
/-- **The pairing of stalks on germs** at a common neighbourhood is the germ of the pairing. -/
theorem fiberPairing_germ {U : X.Etale} (u : Φ.fiber.obj U) (z : ToType (P₁.obj (op U)))
    (s : ToType (P₂.obj (op U))) :
    fiberPairing Φ pair (Φ.toPresheafFiber U u P₁ z) (Φ.toPresheafFiber U u P₂ s) =
      Φ.toPresheafFiber U u P₃ (pair U z s) :=
  toPresheafFiber_pair_eq' Φ pair hpair _ _
    (exists_germ₂ Φ (Φ.toPresheafFiber U u P₁ z) (Φ.toPresheafFiber U u P₂ s)).choose_spec.1
    (exists_germ₂ Φ (Φ.toPresheafFiber U u P₁ z) (Φ.toPresheafFiber U u P₂ s)).choose_spec.2

include hpair in
/-- The pairing of stalks is additive in the first variable when the pairing of sections is. -/
theorem fiberPairing_add_left
    (hadd : ∀ (U : X.Etale) (z z' : ToType (P₁.obj (op U))) (s : ToType (P₂.obj (op U))),
      pair U (z + z') s = pair U z s + pair U z' s)
    (a a' : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) :
    fiberPairing Φ pair (a + a') m = fiberPairing Φ pair a m + fiberPairing Φ pair a' m := by
  obtain ⟨⟨U, u, z, s⟩, rfl, rfl⟩ := exists_germ₂ Φ a m
  obtain ⟨U', u', z', rfl⟩ := Φ.toPresheafFiber_jointly_surjective a'
  obtain ⟨W, w, g, g', rfl, rfl⟩ := exists_fiber_cone Φ u u'
  dsimp only
  rw [toPresheafFiber_fiber_map Φ P₁ g, toPresheafFiber_fiber_map Φ P₂ g,
    toPresheafFiber_fiber_map Φ P₁ g', ← map_add, fiberPairing_germ Φ pair hpair,
    fiberPairing_germ Φ pair hpair, fiberPairing_germ Φ pair hpair, hadd, map_add]

include hpair in
/-- The pairing of stalks commutes with multiples in the second variable when the pairing of
sections does. -/
theorem fiberPairing_nsmul_right
    (hsmul : ∀ (U : X.Etale) (z : ToType (P₁.obj (op U))) (s : ToType (P₂.obj (op U))) (i : ℕ),
      pair U z (i • s) = i • pair U z s)
    (a : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) (i : ℕ) :
    fiberPairing Φ pair a (i • m) = i • fiberPairing Φ pair a m := by
  obtain ⟨⟨U, u, z, s⟩, rfl, rfl⟩ := exists_germ₂ Φ a m
  dsimp only
  rw [← map_nsmul, fiberPairing_germ Φ pair hpair, fiberPairing_germ Φ pair hpair, hsmul,
    map_nsmul]

include hpair in
/-- **Pairing against the germ of `r` is bijective** when pairing against the restrictions of `r`
is bijective on the sections over every refinement of its neighbourhood. -/
theorem bijective_fiberPairing_of_bijective {V : X.Etale} (v : Φ.fiber.obj V)
    (r : ToType (P₂.obj (op V)))
    (hb : ∀ (W : X.Etale) (g : W ⟶ V),
      Function.Bijective (fun z : ToType (P₁.obj (op W)) => pair W z (P₂.map g.op r))) :
    Function.Bijective
      (fun a => fiberPairing Φ pair a (Φ.toPresheafFiber V v P₂ r)) := by
  constructor
  · intro a₁ a₂ h
    obtain ⟨⟨U, u, z₁, z₂⟩, rfl, rfl⟩ := exists_germ₂ (P₂ := P₁) Φ a₁ a₂
    obtain ⟨W, w, g, h', rfl, rfl⟩ := exists_fiber_cone Φ u v
    dsimp only at h ⊢
    rw [toPresheafFiber_fiber_map Φ P₁ g, toPresheafFiber_fiber_map Φ P₁ g,
      toPresheafFiber_fiber_map Φ P₂ h', fiberPairing_germ Φ pair hpair,
      fiberPairing_germ Φ pair hpair] at h
    obtain ⟨Y, f, y, rfl, hf⟩ := (Φ.toPresheafFiber_eq_iff' W w _ _).1 h
    rw [← hpair, ← hpair] at hf
    have := (hb Y (f ≫ h')).1 (show pair Y (P₁.map f.op (P₁.map g.op z₁)) (P₂.map (f ≫ h').op r) =
      pair Y (P₁.map f.op (P₁.map g.op z₂)) (P₂.map (f ≫ h').op r) by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]; exact hf)
    rw [toPresheafFiber_fiber_map Φ P₁ g, toPresheafFiber_fiber_map Φ P₁ g,
      toPresheafFiber_fiber_map Φ P₁ f, toPresheafFiber_fiber_map Φ P₁ f, this]
  · intro c
    obtain ⟨U, u, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective c
    obtain ⟨W, w, g, h', rfl, rfl⟩ := exists_fiber_cone Φ u v
    obtain ⟨z, hz⟩ := (hb W h').2 (P₃.map g.op t)
    refine ⟨Φ.toPresheafFiber W w P₁ z, ?_⟩
    dsimp only at hz ⊢
    rw [toPresheafFiber_fiber_map Φ P₂ h', fiberPairing_germ Φ pair hpair, hz,
      toPresheafFiber_fiber_map Φ P₃ g]

variable {Φ} in
include hpair in
/-- **The pairing of stalks commutes with the maps induced by a morphism of points.** -/
theorem fiberPairing_presheafFiber_hom {Ψ : Point.{w} X.smallEtaleTopology} (f : Ψ ⟶ Φ)
    (a : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) :
    fiberPairing Ψ pair ((Point.Hom.presheafFiber f).app P₁ a)
        ((Point.Hom.presheafFiber f).app P₂ m) =
      (Point.Hom.presheafFiber f).app P₃ (fiberPairing Φ pair a m) := by
  obtain ⟨⟨U, u, z, s⟩, rfl, rfl⟩ := exists_germ₂ Φ a m
  dsimp only
  rw [presheafFiber_hom_app_germ, presheafFiber_hom_app_germ, fiberPairing_germ Ψ pair hpair,
    fiberPairing_germ Φ pair hpair, presheafFiber_hom_app_germ]

variable {Q₁ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₁} {Q₂ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₂}
  {Q₃ : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₃}
  (pair' : ∀ U : X.Etale, ToType (Q₁.obj (op U)) → ToType (Q₂.obj (op U)) → ToType (Q₃.obj (op U)))
  (hpair' : ∀ {U V : X.Etale} (g : V ⟶ U) (z : ToType (Q₁.obj (op U))) (s : ToType (Q₂.obj (op U))),
    pair' V (Q₁.map g.op z) (Q₂.map g.op s) = Q₃.map g.op (pair' U z s))

include hpair hpair' in
/-- **The pairings of stalks commute with maps of presheaves** compatible with the pairings of
sections. -/
theorem fiberPairing_presheafFiber_map (φ₁ : P₁ ⟶ Q₁) (φ₂ : P₂ ⟶ Q₂) (φ₃ : P₃ ⟶ Q₃)
    (h : ∀ (U : X.Etale) (z : ToType (P₁.obj (op U))) (s : ToType (P₂.obj (op U))),
      pair' U (φ₁.app (op U) z) (φ₂.app (op U) s) = φ₃.app (op U) (pair U z s))
    (a : ToType (Φ.presheafFiber.obj P₁)) (m : ToType (Φ.presheafFiber.obj P₂)) :
    fiberPairing Φ pair' (Φ.presheafFiber.map φ₁ a) (Φ.presheafFiber.map φ₂ m) =
      Φ.presheafFiber.map φ₃ (fiberPairing Φ pair a m) := by
  obtain ⟨⟨U, u, z, s⟩, rfl, rfl⟩ := exists_germ₂ Φ a m
  dsimp only
  rw [Point.toPresheafFiber_naturality_apply, Point.toPresheafFiber_naturality_apply,
    fiberPairing_germ Φ pair' hpair', fiberPairing_germ Φ pair hpair,
    Point.toPresheafFiber_naturality_apply, h]

end Pairing

section Twist

variable (N : ℕ) [NeZero N]

omit [UnivLE.{w, u + 1}] [LocallySmall.{w} X.Etale] in
/-- **The restriction of a primitive root of unity**: the section `ζ` of `μ_N` over `V`, restricted
along `g : W ⟶ V`, is the section `ζ` over `W` for the composite structure map. -/
theorem rootsOfUnitySheaf_map_sliceRootSection {V W : X.Etale} (g : W ⟶ V) {k : Type u} [Field k]
    (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N) (m : ZMod N) :
    (rootsOfUnitySheaf.{u, 0} X N).obj.map g.op (sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) m) =
      sliceRootSection.{u, 0} W (g.left.appTop.hom.comp κ) hζ (Over.mk (𝟙 W)) m := by
  apply rootsOfUnityι_app_injective.{u, 0} N W
  have h1 : (rootsOfUnityι.{u, 0} X N).hom.app (op V)
      (sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) m) =
        ofUnit.{u, 0} (sliceRootOn V κ hζ (Over.mk (𝟙 V)) ^ m.val) :=
    rootsOfUnityι_sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) m
  have h2 : (rootsOfUnityι.{u, 0} X N).hom.app (op W)
      (sliceRootSection.{u, 0} W (g.left.appTop.hom.comp κ) hζ (Over.mk (𝟙 W)) m) =
        ofUnit.{u, 0} (sliceRootOn W (g.left.appTop.hom.comp κ) hζ (Over.mk (𝟙 W)) ^ m.val) :=
    rootsOfUnityι_sliceRootSection.{u, 0} W _ hζ (Over.mk (𝟙 W)) m
  rw [NatTrans.naturality_apply, h1, h2, map_ofUnit, map_pow]
  congr 2

variable (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))

/-- **The stalk of `𝓗om(μ_N, G)` is the stalk of `G`**: pairing a germ of `G(-1)` with the germ of
a primitive `N`-th root of unity `ζ`, on a neighbourhood carrying one, is bijective. -/
theorem bijective_twistNegOneFiberPairing_root {V : X.Etale} (v : Φ.fiber.obj V) {k : Type u}
    [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    Function.Bijective (fun a => fiberPairing Φ
      (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s) a
      (Φ.toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
        (sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) 1))) :=
  bijective_fiberPairing_of_bijective Φ _ (twistNegOneModulePairing_naturality.{u, 0} X N G) v _
    (fun W g => by
      change Function.Bijective (fun α => twistNegOneModulePairing.{u, 0} X N G W α
        ((rootsOfUnitySheaf.{u, 0} X N).obj.map g.op
          (sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) 1)))
      rw [rootsOfUnitySheaf_map_sliceRootSection N g κ hζ 1]
      exact bijective_twistNegOneModuleEvalRoot.{u, 0} W _ hζ G)

end Twist

section Transition

variable (ℓ N N' : ℕ) (hN : ℓ * N = N') [NeZero N] [NeZero N'] {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) [NeZero ((N' : ℕ) : k)]
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))
  (G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N')))
  (t : G' ⟶ (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, 0} ℓ N N' hN)).obj G)

omit [UnivLE.{w, u + 1}] [LocallySmall.{w} X.Etale] in
/-- **The transition of the twist on sections**: `⟨τ α', p s'⟩ = t ⟨α', s'⟩`, `τ` the transition
of the twist attached to `t` and `p` the `ℓ`-th power map. -/
theorem twistNegOneModulePairing_transition (U : X.Etale)
    (α' : ToType ((twistNegOneModule.{u, 0} X N' G').obj.obj (op U)))
    (s' : ToType ((rootsOfUnityModule.{u, 0} X N').obj.obj (op U))) :
    twistNegOneModulePairing.{u, 0} X N G U
        ((twistNegOneModuleTransition.{u, 0} X ℓ N N' hN G f G' t).hom.app (op U) α')
        ((rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN).hom.app (op U) s') =
      t.hom.app (op U) (twistNegOneModulePairing.{u, 0} X N' G' U α' s') :=
  congrArg (fun β => β.hom.app (op (Over.mk (𝟙 U))) s') <| congrArg (fun φ => φ.hom.app (op U) α')
    (twistNegOneModuleTransition_comp_precompPow.{u, 0} X ℓ N N' hN G f G' t)

end Transition

end Stacks.Kummer

end
