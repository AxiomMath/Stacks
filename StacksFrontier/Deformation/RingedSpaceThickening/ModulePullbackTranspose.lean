module

public import StacksFrontier.Deformation.RingedSpaceThickening.RestrictedExtensionAction
import StacksCore.Tactic.StacksAttribute

/-!
# Transposes of maps out of iterated pullbacks of modules on ringed spaces

Adjunction bookkeeping for `f^* ⊣ f_*` along composites and commutative squares of morphisms of
ringed spaces: the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` in terms of the units of `f` and `g`, the
agreement of the two spellings `modulePullbackComp` and `modulePullbackCompUniq` of
`(f ≫ g)^* ≅ g^* ⋙ f^*`, the effect of these comparisons and of the comparison of a commutative
square on adjoint transposes, the section of the reduction of `π^* ℱ` for a retraction `π` of a
thickening, and the description of the map `ℐ₂ ⟶ ℐ₁` of a morphism of thickenings
(`thickeningIdealMap`) as the pullback of the ideal-sheaf map of its square.

## References

* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

section Units

variable {X Y Z : RingedSpace.{u, u}}

/-- **The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`** is the unit of `g^* ⊣ g_*` followed by `g_*` of the
unit of `f^* ⊣ f_*`, read through the composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
theorem unit_comp_unit_modulePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (modulePullbackPushforwardAdjunction g).unit.app M ≫
        (modulePushforward g).map ((modulePullbackPushforwardAdjunction f).unit.app
          ((modulePullback g).obj M)) =
      (modulePullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (modulePushforward (f ≫ g)).map ((modulePullbackComp f g).hom.app M) := by
  have h := CategoryTheory.unit_conjugateEquiv ((modulePullbackPushforwardAdjunction g).comp
    (modulePullbackPushforwardAdjunction f)) (modulePullbackPushforwardAdjunction (f ≫ g))
    (modulePullbackComp f g).hom M
  rw [conjugateEquiv_modulePullbackComp_hom, Adjunction.comp_unit_app] at h
  exact (Category.comp_id _).symm.trans h

/-- The unit of the adjunction of a morphism equal to the identity, read through the
identification `g_* ≅ 𝟭`, is the identification `𝟭 ≅ g^*`. -/
theorem unit_comp_eqToHom_modulePushforwardId {g : X ⟶ X} (h : g = 𝟙 X)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction g).unit.app M ≫
        eqToHom (congrArg (fun k : X ⟶ X => (modulePushforward k).obj ((modulePullback g).obj M))
          h) ≫ (modulePushforwardId X).hom.app ((modulePullback g).obj M) =
      (modulePullbackId X).inv.app M ≫ (modulePullbackCongr h).inv.app M := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, modulePullbackCongr, eqToIso_refl, Iso.refl_inv,
    NatTrans.id_app, Category.comp_id]
  rw [modulePullbackPushforwardAdjunction_id_unit_app]
  exact Category.comp_id _

/-- **The section of the reduction of `π^* ℱ`.** For a retraction `π` of `i`, the unit
`ℱ ⟶ π_* π^* ℱ` followed by `π_*` of the canonical map `π^* ℱ ⟶ i_* i^* π^* ℱ` and the
identifications `π_* i_* ≅ 𝟭` and `i^* π^* ≅ (i ≫ π)^* = 𝟙^* ≅ 𝟭` is the identity of `ℱ`. -/
theorem unit_comp_splitRestriction_reduction {X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (π : SplitMono i) (F : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction π.retraction).unit.app F ≫
        (splitRestriction i π).map ((modulePullbackPushforwardAdjunction i).unit.app
          ((modulePullback π.retraction).obj F) ≫ (modulePushforward i).map
            ((modulePullbackComp i π.retraction).symm.app F ≪≫
              (modulePullbackCongr π.id).app F ≪≫ (modulePullbackId X).app F).hom) ≫
        (splitRestrictionIso i π F).hom = 𝟙 F := by
  have hnat : (modulePushforward (i ≫ π.retraction)).map
        ((modulePullbackComp i π.retraction).hom.app F) ≫
        (splitRestrictionIso i π
          ((modulePullback i).obj ((modulePullback π.retraction).obj F))).hom =
      (splitRestrictionIso i π ((modulePullback (i ≫ π.retraction)).obj F)).hom ≫
        (modulePullbackComp i π.retraction).hom.app F :=
    (splitRestrictionCompIso i π).hom.naturality ((modulePullbackComp i π.retraction).hom.app F)
  have hA : (modulePullbackPushforwardAdjunction π.retraction).unit.app F ≫
        (splitRestriction i π).map ((modulePullbackPushforwardAdjunction i).unit.app
          ((modulePullback π.retraction).obj F)) =
      (modulePullbackPushforwardAdjunction (i ≫ π.retraction)).unit.app F ≫
        (modulePushforward (i ≫ π.retraction)).map
          ((modulePullbackComp i π.retraction).hom.app F) :=
    unit_comp_unit_modulePullbackComp i π.retraction F
  have hB : (modulePullbackPushforwardAdjunction (i ≫ π.retraction)).unit.app F ≫
        (splitRestrictionIso i π ((modulePullback (i ≫ π.retraction)).obj F)).hom =
      (modulePullbackId X).inv.app F ≫ (modulePullbackCongr π.id).inv.app F := by
    have hS : (splitRestrictionIso i π ((modulePullback (i ≫ π.retraction)).obj F)).hom =
        eqToHom (congrArg (fun k : X ⟶ X ↦ (modulePushforward k).obj
          ((modulePullback (i ≫ π.retraction)).obj F)) π.id) ≫
          (modulePushforwardId X).hom.app _ := by
      simp only [splitRestrictionIso, splitRestrictionCompIso, Iso.trans_hom, Iso.app_hom,
        NatTrans.comp_app, eqToIso.hom, eqToHom_app, modulePushforwardComp_hom_app]
      exact Category.id_comp _
    rw [hS]
    exact unit_comp_eqToHom_modulePushforwardId π.id F
  have hD : (modulePullbackComp i π.retraction).hom.app F ≫
      ((modulePullbackComp i π.retraction).symm.app F ≪≫
        (modulePullbackCongr π.id).app F ≪≫ (modulePullbackId X).app F).hom =
      (modulePullbackCongr π.id).hom.app F ≫ (modulePullbackId X).hom.app F := by
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [splitRestrictionIso_naturality,
    ← Category.assoc ((modulePullbackPushforwardAdjunction π.retraction).unit.app F), hA]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun z ↦ (modulePullbackPushforwardAdjunction (i ≫ π.retraction)).unit.app F ≫ z)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun z ↦ (modulePullbackPushforwardAdjunction (i ≫ π.retraction)).unit.app F ≫
    z ≫ ((modulePullbackComp i π.retraction).symm.app F ≪≫
        (modulePullbackCongr π.id).app F ≪≫ (modulePullbackId X).app F).hom) hnat).trans ?_
  refine (congrArg
    (fun z ↦ (modulePullbackPushforwardAdjunction (i ≫ π.retraction)).unit.app F ≫ z)
    (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hB, hD]
  simp

/-- **The canonical map `ℳ ⟶ h_* h^* ℳ` is compatible with the two reductions.** For a morphism
`h : X'₁ ⟶ X'₂` of thickenings of `X` (`i₁ ≫ h = i₂`), the unit `ℳ ⟶ h_* h^* ℳ` followed by
`h_*` of the canonical map `h^* ℳ ⟶ (i₁)_* i₁^* h^* ℳ = (i₁)_* i₂^* ℳ` is the canonical map
`ℳ ⟶ (i₂)_* i₂^* ℳ`. -/
theorem unit_comp_pushforward_unit_thickening {X₁ X₂ : RingedSpace.{u, u}} (i₁ : X ⟶ X₁)
    (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (M : SheafOfModules.{u} (structureSheafRing X₂)) :
    (modulePullbackPushforwardAdjunction h).unit.app M ≫
        (modulePushforward h).map ((modulePullbackPushforwardAdjunction i₁).unit.app
          ((modulePullback h).obj M) ≫ (modulePushforward i₁).map
            ((modulePullbackComp i₁ h).symm.app M ≪≫ (modulePullbackCongr comm).app M).hom) =
      (modulePullbackPushforwardAdjunction i₂).unit.app M ≫
        (thickeningPushforwardComp i₁ i₂ h comm).inv.app ((modulePullback i₂).obj M) := by
  subst comm
  rw [Functor.map_comp, ← Category.assoc, unit_comp_unit_modulePullbackComp i₁ h M]
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  show (modulePushforward (i₁ ≫ h)).map ((modulePullbackComp i₁ h).hom.app M) ≫
    (modulePushforward (i₁ ≫ h)).map (((modulePullbackComp i₁ h).symm.app M ≪≫
      (modulePullbackCongr rfl).app M).hom) = _
  rw [← Functor.map_comp]
  simp [thickeningPushforwardComp, modulePullbackCongr]

/-- The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` read through `modulePullbackCompUniq`: the same formula
as `unit_comp_unit_modulePullbackComp`, for the other spelling of the composition isomorphism. -/
theorem unit_comp_unit_modulePullbackCompUniq (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (modulePullbackPushforwardAdjunction g).unit.app M ≫
        (modulePushforward g).map ((modulePullbackPushforwardAdjunction f).unit.app
          ((modulePullback g).obj M)) =
      (modulePullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (modulePushforward (f ≫ g)).map ((modulePullbackCompUniq f g).hom.app M) := by
  let : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g
  let : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (f ≫ g)
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (modulePullbackPushforwardAdjunction (f ≫ g))
    (((modulePullbackPushforwardAdjunction g).comp
      (modulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (modulePushforwardCompSymm f g).symm) M
  refine Eq.trans ?_ h.symm
  simp only [Adjunction.ofNatIsoRight, modulePushforwardCompSymm, Functor.id_obj,
    Functor.comp_obj, Iso.symm_symm_eq, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, modulePushforwardComp_hom_app]
  exact (Category.comp_id _).symm

/-- **The two spellings of the composition isomorphism of pullbacks agree.** -/
theorem modulePullbackCompUniq_eq_modulePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompUniq f g = modulePullbackComp f g := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  apply ((modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← unit_comp_unit_modulePullbackCompUniq, ← unit_comp_unit_modulePullbackComp]

/-- **`(𝟙 ≫ g)^* ≅ g^* ⋙ (𝟙)^*` is the identification `(𝟙)^* ≅ 𝟭`.** -/
theorem modulePullbackComp_id_hom_app (g : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullbackComp (𝟙 X) g).hom.app M =
      (modulePullbackId X).inv.app ((modulePullback g).obj M) := by
  have h := unit_comp_unit_modulePullbackComp (𝟙 X) g M
  rw [modulePullbackPushforwardAdjunction_id_unit_app] at h
  apply ((modulePullbackPushforwardAdjunction g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact h.symm

/-- **The map `ℐ₂ ⟶ ℐ₁` of a morphism of thickenings is the pullback of the ideal-sheaf map of the
square.** `thickeningIdealMap` is `i₁^*` of `Stacks.ClosedImmersion.idealSheafMap` of the square
`i₁ ≫ h = 𝟙 ≫ i₂`, read through `(i₁ ≫ h)^* ≅ h^* ⋙ i₁^*`. -/
theorem thickeningIdealMap_eq {X₁ X₂ : RingedSpace.{u, u}} (i₁ : X ⟶ X₁)
    (h : X₁ ⟶ X₂) :
    thickeningIdealMap i₁ (i₁ ≫ h) h rfl =
      (modulePullbackComp i₁ h).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h)) ≫
        (modulePullback i₁).map (Stacks.ClosedImmersion.idealSheafMap
          (comp_eq_id_comp (rfl : i₁ ≫ h = i₁ ≫ h))) := by
  have key : (modulePullbackId X).inv.app ((modulePullback (i₁ ≫ h)).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h))) ≫
      (modulePullbackComp (𝟙 X) (i₁ ≫ h)).inv.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h)) = 𝟙 _ := by
    rw [← modulePullbackComp_id_hom_app]
    exact (modulePullbackComp (𝟙 X) (i₁ ≫ h)).hom_inv_id_app _
  have h2 := congrArg (· ≫ (modulePullbackComp i₁ h).hom.app
    (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h)) ≫ (modulePullback i₁).map
      (Stacks.ClosedImmersion.idealSheafMap (comp_eq_id_comp (rfl : i₁ ≫ h = i₁ ≫ h)))) key
  exact h2.trans (Category.id_comp _)

/-! ### Transposes across composites -/

/-- **Transposing across a composite.** Transposing along `f ≫ g` a map out of `(f ≫ g)^* 𝒩`
which is read through `(f ≫ g)^* 𝒩 ≅ f^* g^* 𝒩` is transposing in two steps, along `f` and then
along `g`. -/
theorem homEquiv_modulePullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : SheafOfModules.{u} (structureSheafRing Z)) {Q : SheafOfModules.{u} (structureSheafRing X)}
    (δ : (modulePullback f).obj ((modulePullback g).obj N) ⟶ Q) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        ((modulePullbackComp f g).hom.app N ≫ δ) =
      (modulePullbackPushforwardAdjunction g).homEquiv _ _
        ((modulePullbackPushforwardAdjunction f).homEquiv _ _ δ) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_comp_unit_modulePullbackComp, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp]
  exact Category.assoc _ _ _

/-- The pushforwards along equal morphisms agree, naturally. -/
theorem eqToHom_modulePushforward_map {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂)
    {P Q : SheafOfModules.{u} (structureSheafRing X)} (φ : P ⟶ Q) :
    (modulePushforward k₁).map φ ≫
        eqToHom (congrArg (fun k : X ⟶ Y => (modulePushforward k).obj Q) e) =
      eqToHom (congrArg (fun k : X ⟶ Y => (modulePushforward k).obj P) e) ≫
        (modulePushforward k₂).map φ := by
  subst e
  simp

/-- **Transposing around a commutative square.** For `j₁ ≫ b = a ≫ j₂`, transposing along `a`
and then `j₂` a map out of `a^* j₂^* 𝒩` that is read through the comparison
`j₁^* b^* 𝒩 ≅ a^* j₂^* 𝒩` is transposing along `j₁` and then `b`, followed by the comparison
`b_* (j₁)_* ≅ (j₂)_* a_*`. -/
theorem homEquiv_modulePullbackSquareIso_inv {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂)
    (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁) (j₂ : Z₂ ⟶ X₂) (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing X₂))
    {Q : SheafOfModules.{u} (structureSheafRing Z₁)}
    (γ : (modulePullback j₁).obj ((modulePullback b).obj N) ⟶ Q) :
    (modulePullbackPushforwardAdjunction j₂).homEquiv _ _
        ((modulePullbackPushforwardAdjunction a).homEquiv _ _
          ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app N ≫ γ)) =
      (modulePullbackPushforwardAdjunction b).homEquiv _ _
          ((modulePullbackPushforwardAdjunction j₁).homEquiv _ _ γ) ≫
        (modulePushforwardSquareIso a b j₁ j₂ comm).hom.app Q := by
  have hn := (modulePushforwardSquareIso a b j₁ j₂ comm).hom.naturality
    ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app N ≫ γ)
  calc (modulePullbackPushforwardAdjunction j₂).homEquiv _ _
        ((modulePullbackPushforwardAdjunction a).homEquiv _ _
          ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app N ≫ γ))
      = ((modulePullbackPushforwardAdjunction j₂).unit.app N ≫
          (modulePushforward j₂).map
            ((modulePullbackPushforwardAdjunction a).unit.app ((modulePullback j₂).obj N))) ≫
          (modulePushforward a ⋙ modulePushforward j₂).map
            ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app N ≫ γ) := by
        simp only [Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = ((modulePullbackPushforwardAdjunction b).unit.app N ≫
          (modulePushforward b).map
            ((modulePullbackPushforwardAdjunction j₁).unit.app ((modulePullback b).obj N))) ≫
          (modulePushforward j₁ ⋙ modulePushforward b).map
            ((modulePullbackSquareIso a b j₁ j₂ comm).hom.app N) ≫
          (modulePushforward j₁ ⋙ modulePushforward b).map
            ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app N ≫ γ) ≫
          (modulePushforwardSquareIso a b j₁ j₂ comm).hom.app Q := by
        rw [hn, ← unit_modulePullbackSquareIso a b j₁ j₂ comm N]
        simp only [Category.assoc]
        rfl
    _ = _ := by
        simp only [Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp, Category.assoc]
        congr 2
        simp only [← Functor.map_comp_assoc]
        rw [Iso.hom_inv_id_app]
        exact congrArg (fun z ↦ (modulePushforward b).map z ≫ _)
          ((congrArg (· ≫ _) ((modulePushforward j₁).map_id _)).trans (Category.id_comp _))

/-- `homEquiv_modulePullbackComp_hom` with the comparison `g_* f_* ≅ (f ≫ g)_*` written out. -/
theorem homEquiv_modulePullbackComp_hom' (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : SheafOfModules.{u} (structureSheafRing Z)) {Q : SheafOfModules.{u} (structureSheafRing X)}
    (δ : (modulePullback f).obj ((modulePullback g).obj N) ⟶ Q) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        ((modulePullbackComp f g).hom.app N ≫ δ) =
      (modulePullbackPushforwardAdjunction g).homEquiv _ _
          ((modulePullbackPushforwardAdjunction f).homEquiv _ _ δ) ≫
        (modulePushforwardComp f g).hom.app Q := by
  rw [homEquiv_modulePullbackComp_hom, modulePushforwardComp_hom_app]
  exact (Category.comp_id _).symm

/-- The comparison of the two composites of pushforwards around a commutative square is natural. -/
theorem modulePushforwardComp_eqToHom_naturality {A B C D : RingedSpace.{u, u}} (a : A ⟶ B)
    (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d)
    {P Q : SheafOfModules.{u} (structureSheafRing A)} (φ : P ⟶ Q) :
    (modulePushforwardComp a b).hom.app P ≫
        eqToHom (congrArg (fun k : A ⟶ D => (modulePushforward k).obj P) e) ≫
        (modulePushforwardComp c d).inv.app P ≫
          (modulePushforward d).map ((modulePushforward c).map φ) =
      (modulePushforward b).map ((modulePushforward a).map φ) ≫
        (modulePushforwardComp a b).hom.app Q ≫
        eqToHom (congrArg (fun k : A ⟶ D => (modulePushforward k).obj Q) e) ≫
        (modulePushforwardComp c d).inv.app Q := by
  have h1 := (modulePushforwardComp c d).inv.naturality φ
  have h2 := (modulePushforwardComp a b).hom.naturality φ
  simp only [Functor.comp_map] at h1 h2
  rw [← h1, ← reassoc_of% eqToHom_modulePushforward_map e φ, reassoc_of% h2]

end Units

end AlgebraicGeometry.RingedSpaceThickening
