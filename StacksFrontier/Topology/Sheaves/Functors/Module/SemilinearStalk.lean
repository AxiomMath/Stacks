module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.Sheaves.Functors.Module.InverseImage

/-!
# Semilinear identifications of stalks of pullback sheaves of modules

Let `f : X ⟶ Y` be a continuous map, `O` a presheaf of rings on `Y` and `G` a presheaf of
`O`-modules. The isomorphism `TopCat.Presheaf.stalkPullbackIso` identifies the stalks at `x` of
the pullbacks `Stacks.PresheafOfModules.Pullback.pullbackRing` of `O` and
`Stacks.PresheafOfModules.Pullback.pullbackAb` of `G` with the stalks of `O` and `G` at `f x`.
These identifications are compatible with the scalar action: `θ_G (a • m) = θ_O a • θ_G m`.

## Main results

* `SemilinearStalk.stalkMap_smul`: a morphism `φ : M ⟶ (restrictScalars ρ).obj N` of
  presheaves of modules over a morphism `ρ : R ⟶ R'` of presheaves of rings induces a map on
  stalks which is semilinear over the stalk map of `ρ`.
* `SemilinearStalk.pbModStalkIso_smul`: the additive isomorphism `G_{f x} ≅ (f_p G)_x` is
  semilinear over the ring isomorphism `O_{f x} ≅ (f_p O)_x`.
* `SemilinearStalk.invModStalkIso_smul`: for the inverse image `f⁻¹` (`f_p` followed by
  sheafification), the additive isomorphism `G_{f x} ≅ (f⁻¹G)_x` is semilinear over the ring
  isomorphism `O_{f x} ≅ (f⁻¹O)_x`.
* `SemilinearStalk.restrictScalars_stalk_smul`: the action of `R_x` on the stalk of `N`
  obtained by restricting scalars along `ι : R ⟶ R'` is the action of `R'_x` along the stalk
  map of `ι`.
* `SemilinearStalk.comm_smul_eq`: the actions on a stalk of the `CommRingCat`-valued and the
  `RingCat`-valued stalks of a presheaf of commutative rings agree.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Opposite Stacks.PresheafOfModules.Pullback

universe u

namespace SemilinearStalk

/-- A stalk element of a ring-valued and one of an `Ab`-valued presheaf are germs of sections
over a common open neighbourhood. -/
private theorem exists_germ_eq_pair {X : TopCat.{u}} (F : TopCat.Presheaf RingCat.{u} X)
    (G : TopCat.Presheaf Ab.{u} X) {x : X} (s : F.stalk x) (t : G.stalk x) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : F.obj (op U)) (m : G.obj (op U)),
      F.germ U x hx a = s ∧ G.germ U x hx m = t := by
  obtain ⟨U₁, hU₁, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq F s
  obtain ⟨U₂, hU₂, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G t
  exact ⟨U₁ ⊓ U₂, ⟨hU₁, hU₂⟩, F.map (homOfLE inf_le_left).op a, G.map (homOfLE inf_le_right).op m,
    TopCat.Presheaf.germ_res_apply F _ x _ a, TopCat.Presheaf.germ_res_apply G _ x _ m⟩

/-! ### Semilinearity of a stalk map along a restriction of scalars -/

section StalkMap

variable {X : TopCat.{u}} {R R' : TopCat.Presheaf RingCat.{u} X} (ρ : R ⟶ R')
  {M : PresheafOfModules.{u} R} {N : PresheafOfModules.{u} R'}
  (φ : M ⟶ (PresheafOfModules.restrictScalars ρ).obj N) (x : X)

/-- The map on stalks of abelian groups induced by a morphism of presheaves of modules
along a restriction of scalars. -/
noncomputable def stalkMap :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x ⟶
      TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((PresheafOfModules.toPresheaf R).map φ)

/-- The map on stalks of rings induced by `ρ`. -/
noncomputable def ringStalkMap : R.stalk x ⟶ R'.stalk x :=
  (TopCat.Presheaf.stalkFunctor RingCat.{u} x).map ρ

/-- Germwise description of `stalkMap`. -/
theorem stalkMap_germ (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    stalkMap ρ φ x (TopCat.Presheaf.germ M.presheaf U x hx m)
      = TopCat.Presheaf.germ N.presheaf U x hx (PresheafOfModules.Hom.app φ (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf R).map φ) m

/-- Germwise description of `ringStalkMap`. -/
theorem ringStalkMap_germ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) :
    ringStalkMap ρ x (R.germ U x hx r) = R'.germ U x hx (ρ.app (op U) r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ρ r

/-- Semilinearity of `stalkMap` on germs. -/
theorem stalkMap_germ_smul (U : Opens X) (hx : x ∈ U) (a : R.obj (op U)) (m : M.obj (op U)) :
    stalkMap ρ φ x (TopCat.Presheaf.germ M.presheaf U x hx (a • m))
      = ringStalkMap ρ x (R.germ U x hx a) •
        stalkMap ρ φ x (TopCat.Presheaf.germ M.presheaf U x hx m) := by
  rw [stalkMap_germ, stalkMap_germ, ringStalkMap_germ,
    (PresheafOfModules.Hom.app φ (op U)).hom.map_smul]
  exact PresheafOfModules.germ_ringCat_smul N x U hx _ _

/-- **Semilinearity of `stalkMap`.**  A morphism of presheaves of modules over a morphism
`ρ` of presheaves of rings induces a stalk map which is semilinear over `ringStalkMap ρ`. -/
theorem stalkMap_smul (r : R.stalk x) (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkMap ρ φ x (r • m) = ringStalkMap ρ x r • stalkMap ρ φ x m := by
  obtain ⟨U, hx, a, n, rfl, rfl⟩ := exists_germ_eq_pair R M.presheaf r m
  have key := stalkMap_germ_smul ρ φ x U hx a n
  erw [PresheafOfModules.germ_ringCat_smul M x U hx] at key
  exact key

end StalkMap

/-! ### The presheaf-level pullback -/

section Pullback

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The pullback presheaf `f_p G` as a presheaf of `f_p O`-modules. -/
noncomputable def pbModPresheaf (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) :
    PresheafOfModules.{u} (pullbackRing f O) :=
  (pullbackModuleFunctor f O).obj G

/-- The comparison isomorphism of rings `O_{f x} ≅ (f_p O)_x`. -/
noncomputable def pbRingStalkIso (O : TopCat.Presheaf RingCat.{u} Y) (x : X) :
    O.stalk (f x) ≅ (pullbackRing f O).stalk x :=
  TopCat.Presheaf.stalkPullbackIso RingCat.{u} f O x

/-- The comparison isomorphism of abelian groups `G_{f x} ≅ (f_p G)_x`. -/
noncomputable def pbModStalkIso (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) G.presheaf (f x) ≅
      TopCat.Presheaf.stalk (C := Ab.{u}) (pbModPresheaf f O G).presheaf x :=
  TopCat.Presheaf.stalkPullbackIso Ab.{u} f G.presheaf x

/-- `pbModStalkIso` sends the germ of `s` at `f x` to the germ over `f⁻¹V` of the unit
image of `s`. -/
theorem pbModStalkIso_germ (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (x : X) (V : Opens Y) (hV : f x ∈ V) (s : G.obj (op V)) :
    (pbModStalkIso f O G x).hom (TopCat.Presheaf.germ G.presheaf V (f x) hV s)
      = TopCat.Presheaf.germ (pbModPresheaf f O G).presheaf ((Opens.map f).obj V) x hV
          (pullbackAbUnit f (underlyingAb O G) (op V) s) := by
  rw [pullbackAbUnit_eq_adjunction_unit, pbModStalkIso]
  exact congrArg (fun φ ↦ (ConcreteCategory.hom φ) s)
    (TopCat.Presheaf.germ_stalkPullbackHom Ab.{u} f G.presheaf x V hV)

/-- The ring analogue of `pbModStalkIso_germ`. -/
theorem pbRingStalkIso_germ (O : TopCat.Presheaf RingCat.{u} Y)
    (x : X) (V : Opens Y) (hV : f x ∈ V) (s : O.obj (op V)) :
    (pbRingStalkIso f O x).hom (O.germ V (f x) hV s)
      = (pullbackRing f O).germ ((Opens.map f).obj V) x hV
          (pullbackRingUnit f O (op V) s) := by
  rw [pullbackRingUnit_eq_adjunction_unit, pbRingStalkIso]
  exact congrArg (fun φ ↦ (ConcreteCategory.hom φ) s)
    (TopCat.Presheaf.germ_stalkPullbackHom RingCat.{u} f O x V hV)

/-- Semilinearity of `pbModStalkIso` on germs, i.e. the case of a scalar and a section
defined over a common open `V ∋ f x`. -/
theorem pbModStalkIso_germ_smul (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O)
    (x : X) (V : Opens Y) (hV : f x ∈ V) (a : O.obj (op V)) (m : G.obj (op V)) :
    (pbModStalkIso f O G x).hom (TopCat.Presheaf.germ G.presheaf V (f x) hV (a • m))
      = (pbRingStalkIso f O x).hom (O.germ V (f x) hV a) •
        (pbModStalkIso f O G x).hom (TopCat.Presheaf.germ G.presheaf V (f x) hV m) := by
  rw [pbModStalkIso_germ, pbModStalkIso_germ, pbRingStalkIso_germ,
    pullbackModule_unit_smul]
  exact PresheafOfModules.germ_ringCat_smul (pbModPresheaf f O G) x ((Opens.map f).obj V) hV _ _

/-- **Semilinearity of the presheaf-level pullback stalk isomorphism.**

The additive isomorphism `G_{f x} ≅ (f_p G)_x` is semilinear over the ring isomorphism
`O_{f x} ≅ (f_p O)_x`. -/
theorem pbModStalkIso_smul (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (x : X)
    (a : O.stalk (f x)) (m : TopCat.Presheaf.stalk (C := Ab.{u}) G.presheaf (f x)) :
    (pbModStalkIso f O G x).hom (a • m)
      = (pbRingStalkIso f O x).hom a • (pbModStalkIso f O G x).hom m := by
  obtain ⟨V, hV, b, n, rfl, rfl⟩ := exists_germ_eq_pair O G.presheaf a m
  have key := pbModStalkIso_germ_smul f O G x V hV b n
  erw [PresheafOfModules.germ_ringCat_smul G (f x) V hV] at key
  exact key

end Pullback

/-! ### The sheaf-level inverse image `f⁻¹`, which is `f_p` followed by sheafification -/

section InverseImage

open InverseImageModules

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Sheaf RingCat.{u} Y)
  (G : SheafOfModules.{u} O)

/-- The sheafification map `f_p G ⟶ f⁻¹G` as a morphism of presheaves of `f_p O`-modules
(over the sheafification map `f_p O ⟶ f⁻¹O` of the base). -/
noncomputable def toInverseImageModules :
    pbModPresheaf f O.obj G.val ⟶
      (PresheafOfModules.restrictScalars (toInverseImageRing f O)).obj
        (inverseImageSheafOfModules f O G).val :=
  PresheafOfModules.toSheafify (toInverseImageRing f O) (toInverseImageAb f O G)

/-- Sheafification does not change the stalk of the presheaf of rings. -/
instance isIso_ringStalkMap (x : X) : IsIso (ringStalkMap (toInverseImageRing f O) x) := by
  rw [ringStalkMap, toInverseImageRing]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x RingCat.{u} _

/-- Sheafification does not change the stalk of the presheaf of abelian groups. -/
instance isIso_stalkMap (x : X) :
    IsIso (stalkMap (X := X) (toInverseImageRing f O) (toInverseImageModules f O G) x) := by
  rw [stalkMap]
  have h : (PresheafOfModules.toPresheaf (pullbackRing f O.obj)).map
      (toInverseImageModules f O G) = toInverseImageAb f O G := rfl
  rw [h, toInverseImageAb]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _

/-- The comparison isomorphism of rings `O_{f x} ≅ (f⁻¹O)_x`. -/
noncomputable def invRingStalkIso (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj (f x) ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) (inverseImageRing f O).obj x :=
  pbRingStalkIso (X := X) (Y := Y) f O.obj x ≪≫
    asIso (ringStalkMap (X := X) (toInverseImageRing f O) x)

/-- The comparison isomorphism of abelian groups `G_{f x} ≅ (f⁻¹G)_x`. -/
noncomputable def invModStalkIso (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x) ≅
      TopCat.Presheaf.stalk (C := Ab.{u}) (inverseImageSheafOfModules f O G).val.presheaf x :=
  pbModStalkIso (X := X) (Y := Y) f O.obj G.val x ≪≫
    asIso (stalkMap (X := X) (toInverseImageRing f O) (toInverseImageModules f O G) x)

/-- **Semilinearity of the inverse-image stalk isomorphism.**

The additive isomorphism `G_{f x} ≅ (f⁻¹G)_x` is semilinear over the ring isomorphism
`O_{f x} ≅ (f⁻¹O)_x`. -/
theorem invModStalkIso_smul (x : X)
    (a : TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj (f x))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)) :
    (invModStalkIso f O G x).hom (a • m)
      = (invRingStalkIso f O x).hom a • (invModStalkIso f O G x).hom m := by
  rw [invModStalkIso, invRingStalkIso]
  simp only [Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply]
  rw [pbModStalkIso_smul, stalkMap_smul]

end InverseImage

/-! ### Restriction of scalars does not change the stalk -/

section RestrictScalars

variable {X : TopCat.{u}} {R R' : TopCat.Presheaf RingCat.{u} X} (ι : R ⟶ R')
  (N : PresheafOfModules.{u} R') (x : X)

/-- The `R_x`-module structure on the stalk of `N` at `x` obtained by restricting scalars
along `ι`: the `R_x`-action on the stalk of `(restrictScalars ι).obj N`. -/
@[instance_reducible] noncomputable def restrictScalarsStalkModule :
    Module (R.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) :=
  inferInstanceAs (Module (R.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u})
      ((PresheafOfModules.restrictScalars ι).obj N).presheaf x))

/-- The `R_x`-action on the stalk of `N` obtained by restricting scalars along `ι` is the
`R'_x`-action along `ringStalkMap ι`. -/
theorem restrictScalars_stalk_smul (r : R.stalk x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) :
    letI := restrictScalarsStalkModule ι N x
    r • m = ringStalkMap ι x r • m := by
  have h := stalkMap_smul ι (𝟙 ((PresheafOfModules.restrictScalars ι).obj N)) x r m
  have e : stalkMap ι (𝟙 ((PresheafOfModules.restrictScalars ι).obj N)) x
      = 𝟙 (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) := by
    rw [stalkMap, CategoryTheory.Functor.map_id]
    exact (TopCat.Presheaf.stalkFunctor Ab.{u} x).map_id _
  rwa [e] at h

end RestrictScalars

/-! ### Comparing the `CommRingCat` and `RingCat` stalk actions

Mathlib puts two module structures on the stalk of a presheaf of modules `M` over
`R ⋙ forget₂ CommRingCat.{u} RingCat.{u}`: one over the `RingCat`-valued stalk of `R ⋙ forget₂`
(`PresheafOfModules.germ_ringCat_smul`) and one over the `CommRingCat`-valued stalk of `R`
(`PresheafOfModules.germ_smul`). They agree through the canonical comparison isomorphism. -/

section CommRing

variable {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)

/-- The comparison isomorphism `(R ⋙ forget₂)_x ≅ R_x` given by the preservation of the
filtered colimit computing the stalk by `forget₂ CommRingCat RingCat`. -/
noncomputable def commStalkIso :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x) :=
  (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R)).symm

/-- `commStalkIso` as a ring equivalence of the underlying rings. -/
noncomputable def commStalkRingEquiv :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x) ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x) :=
  (commStalkIso R x).ringCatIsoToRingEquiv

/-- `commStalkRingEquiv` matches the germ maps. -/
theorem commStalkRingEquiv_germ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) :
    commStalkRingEquiv R x
        (TopCat.Presheaf.germ (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r)
      = R.germ U x hx r :=
  congrArg (fun φ ↦ (ConcreteCategory.hom φ) r) <| ι_preservesColimitIso_inv
    (forget₂ CommRingCat.{u} RingCat.{u}) ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)

/-- On germs the two stalk actions agree. -/
theorem comm_smul_germ (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m
      = TopCat.Presheaf.germ (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r •
        TopCat.Presheaf.germ M.presheaf U x hx m :=
  (PresheafOfModules.germ_smul M x U hx r m).symm.trans
    (PresheafOfModules.germ_ringCat_smul M x U hx r m)

/-- **The `CommRingCat` and `RingCat` stalk actions agree** through `commStalkRingEquiv`. -/
theorem comm_smul_eq (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (s : TopCat.Presheaf.stalk (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    commStalkRingEquiv R x s • m = s • m := by
  obtain ⟨U, hx, r, n, rfl, rfl⟩ :=
    exists_germ_eq_pair (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) M.presheaf s m
  rw [commStalkRingEquiv_germ]
  exact comm_smul_germ R x M U hx _ _

end CommRing

end SemilinearStalk
