module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.OpenRingMap

/-!
# The glued morphism pulls an affine open `V` back to `W_V`

Let `g` be a morphism of *locally* ringed topoi between the small étale ringed topoi of `X` and
`Y`, and let `f : X ⟶ Y` be the morphism of schemes glued in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.OpenRingMap` from
the morphisms `f_V : W_V ⟶ V` over the affine opens `V` of `Y`.  This module proves
`f⁻¹(V) = W_V` (`AlgebraicGeometry.preimage_glueHom_eq`), i.e. `g⁻¹h_V ≅ h_{f⁻¹V}`.

This is where local ringedness enters the Zariski part of the argument.  For a section `b` of
`𝒪_Y` over `V`, the sheaf represented by the basic open `D(b)` is the pullback of the units
subsheaf `𝒪_Y^× ⊆ 𝒪_Y` along `b : h_V ⟶ 𝒪_Y`
(`AlgebraicGeometry.isPullback_basicOpenUnitsHom`).  The inverse image preserves that pullback,
and the square of units of a morphism of locally ringed topoi is cartesian (Stacks 04HA); pasting,
`g⁻¹h_{D(b)}` is the pullback of `𝒪_X^×` along `φ_V b`, i.e. `h_{D(φ_V b)}`
(`AlgebraicGeometry.inverseImageOpen_eq_of_basicOpen`).  As `f_V⁻¹D(b) = D(φ_V b)`, the opens
`W_V` and `f⁻¹V` agree on a basis.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-- A global function of a scheme is a unit exactly when its basic open is everything. -/
theorem Scheme.isUnit_iff_basicOpen_eq_top {T : Scheme.{u}} (c : Γ(T, ⊤)) :
    IsUnit c ↔ T.basicOpen c = ⊤ := by
  refine ⟨Scheme.basicOpen_of_isUnit _, fun h => ?_⟩
  refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ c fun x hx => ?_
  exact (Scheme.mem_basicOpen T c x hx).1 (by rw [h]; trivial)

section BasicOpen

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An object of the small étale site maps into the basic open `D(b) ⊆ V` exactly when `b`
becomes a unit on it.** -/
theorem nonempty_hom_basicOpen_iff {V D : S.Opens}
    (b : Γ((SmallEtale.toScheme B S hS).obj ((opensToBoundedEtale B S hS).obj V), ⊤))
    (hD : V.ι ⁻¹ᵁ D = V.toScheme.basicOpen b) {T : SmallEtale B S hS}
    (k : T ⟶ (opensToBoundedEtale B S hS).obj V) :
    Nonempty (T ⟶ (opensToBoundedEtale B S hS).obj D) ↔
      IsUnit (smallEtaleRestrict B S hS k b) := by
  rw [nonempty_hom_opensToBoundedEtale_iff, Scheme.isUnit_iff_basicOpen_eq_top,
    show ((SmallEtale.toScheme B S hS).obj T).basicOpen (smallEtaleRestrict B S hS k b) =
      (SmallEtale.toScheme B S hS).map k ⁻¹ᵁ (V.toScheme.basicOpen b) from
      (Scheme.preimage_basicOpen_top _ b).symm, ← hD]
  have hk : smallEtaleMap B S hS T = (SmallEtale.toScheme B S hS).map k ≫ V.ι :=
    (smallEtaleStructureHom_comp B S hS k).symm
  rw [hk]
  refine ⟨fun h => eq_top_iff.2 fun t _ => h ⟨t, rfl⟩, ?_⟩
  rintro h _ ⟨t, rfl⟩
  exact (h ▸ trivial : t ∈ ((SmallEtale.toScheme B S hS).map k) ⁻¹ᵁ (V.ι ⁻¹ᵁ D))

variable {V D : S.Opens} (hDV : D ≤ V)
  (b : Γ((SmallEtale.toScheme B S hS).obj ((opensToBoundedEtale B S hS).obj V), ⊤))
  (hD : V.ι ⁻¹ᵁ D = V.toScheme.basicOpen b)
include hD

/-- The value of `b` on a chart of `D(b)`, which is a unit. -/
theorem isUnit_basicOpen_restrict {T : SmallEtale B S hS}
    (m : T ⟶ (opensToBoundedEtale B S hS).obj D) :
    IsUnit (smallEtaleRestrict B S hS (m ≫ (opensToBoundedEtale B S hS).map (homOfLE hDV)) b) :=
  (nonempty_hom_basicOpen_iff B S hS b hD _).1 ⟨m⟩

/-- **`b`, restricted to `D(b)`, as a section of the units subsheaf.** -/
def basicOpenUnitsHom :
    openSheaf B S hS D ⟶
      RingedTopos.units (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)) :=
  ⟨{ app := fun T => TypeCat.ofHom fun (m : T.unop ⟶ (opensToBoundedEtale B S hS).obj D) =>
       (isUnit_basicOpen_restrict B S hS hDV b hD m).unit
     naturality := fun T T' k => TypeCat.homEquiv.injective (funext
      fun (m : T.unop ⟶ (opensToBoundedEtale B S hS).obj D) => Units.ext (by
        change smallEtaleRestrict B S hS ((k.unop ≫ m) ≫ _) b =
          smallEtaleRestrict B S hS k.unop (smallEtaleRestrict B S hS (m ≫ _) b)
        rw [Category.assoc]
        simp only [smallEtaleRestrict, Functor.map_comp, Scheme.Hom.comp_appTop,
          CommRingCat.hom_comp, RingHom.comp_apply])) }⟩

/-- Composing `basicOpenUnitsHom` with the inclusion of the units into the structure sheaf gives
the section `b` precomposed with the restriction `h_D ⟶ h_V`. -/
theorem basicOpenUnitsHom_comp_unitsι :
    basicOpenUnitsHom B S hS hDV b hD ≫
        RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)) =
      openSheafMap B S hS hDV ≫
        (smallEtaleSectionRingEquiv B S hS ((opensToBoundedEtale B S hS).obj V)).symm b := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T => TypeCat.homEquiv.injective
    (funext fun (m : T.unop ⟶ (opensToBoundedEtale B S hS).obj D) => ?_)))
  change smallEtaleRestrict B S hS (m ≫ _) b =
    ((smallEtaleSectionRingEquiv B S hS ((opensToBoundedEtale B S hS).obj V)).symm b).hom.app T
      (m ≫ (opensToBoundedEtale B S hS).map (homOfLE hDV))
  rw [smallEtaleSectionRingEquiv_symm_hom_app]

/-- A morphism `c : Z ⟶ h_V` along which `b` lifts to the units subsheaf takes values in charts
of `D(b)`. -/
theorem nonempty_hom_basicOpen_of_comp {Z : Sheaf (SmallEtale.topology B S hS) (Type u)}
    (a : Z ⟶ RingedTopos.units (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)))
    (c : Z ⟶ openSheaf B S hS V)
    (hac : a ≫ RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)) =
      c ≫ (smallEtaleSectionRingEquiv B S hS ((opensToBoundedEtale B S hS).obj V)).symm b)
    (T : (SmallEtale B S hS)ᵒᵖ) (z : Z.obj.obj T) :
    Nonempty ((openSheaf B S hS D).obj.obj T) := by
  let Γ' := ↥Γ((SmallEtale.toScheme B S hS).obj T.unop, ⊤)
  have h : ((show Γ'ˣ from a.hom.app T z) : Γ') =
      smallEtaleRestrict B S hS (c.hom.app T z) b :=
    (congrArg (fun α : Z ⟶ (RingedSite.toRingedTopos
      (smallEtaleRingedSite B S hS)).forgetRing.obj
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O => α.hom.app T z) hac).trans
      (smallEtaleSectionRingEquiv_symm_hom_app B S hS _ b T (c.hom.app T z))
  exact (nonempty_hom_basicOpen_iff B S hS b hD (c.hom.app T z)).2 (h ▸ Units.isUnit _)

/-- **`h_{D(b)}` is the pullback of the units subsheaf along `b : h_V ⟶ 𝒪_S`.** -/
theorem isPullback_basicOpenUnitsHom :
    IsPullback (basicOpenUnitsHom B S hS hDV b hD) (openSheafMap B S hS hDV)
      (RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)))
      ((smallEtaleSectionRingEquiv B S hS ((opensToBoundedEtale B S hS).obj V)).symm b) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (basicOpenUnitsHom_comp_unitsι B S hS hDV b hD)
    (fun s => homOfSubsingleton B S hS (fun U => subsingleton_openSheaf_obj B S hS D U)
      (nonempty_hom_basicOpen_of_comp B S hS b hD s.fst s.snd s.condition)) ?_ ?_ ?_)
  · intro s
    have := RingedTopos.unitsι_mono (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
    rw [← cancel_mono
      (RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))),
      Category.assoc, basicOpenUnitsHom_comp_unitsι]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (isSubterminal_openSheaf B S hS V _ _)).trans s.condition.symm)
  · exact fun _ => isSubterminal_openSheaf B S hS V _ _
  · exact fun _ _ _ _ => isSubterminal_openSheaf B S hS D _ _

end BasicOpen

/-! ### Transport of the basic open along a locally ringed `g` -/

section Transport

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- **`g⁻¹h_{D(b)} ≅ h_{D(φ_V b)}` for a morphism of locally ringed topoi.**  Stated with the two
basic opens described by their preimages in `V` and in `W_V`. -/
theorem inverseImageOpen_eq_of_basicOpen (hg : g.IsLocallyRinged) {V D : Y.obj.Opens}
    (hDV : D ≤ V)
    (b : Γ((SmallEtale.toScheme B Y.obj Y.property).obj
      ((opensToBoundedEtale B Y.obj Y.property).obj V), ⊤))
    (hD : V.ι ⁻¹ᵁ D = V.toScheme.basicOpen b)
    {D' : X.obj.Opens} (hD'W : D' ≤ inverseImageOpen B X Y g V)
    (hD' : (inverseImageOpen B X Y g V).ι ⁻¹ᵁ D' =
      (inverseImageOpen B X Y g V).toScheme.basicOpen (openRingHom g V b)) :
    inverseImageOpen B X Y g D = D' := by
  obtain ⟨t, hLR⟩ := hg
  let := g.toToposHom.preservesFiniteLimits
  let Φ := g.toToposHom.inverseImage
  let e := inverseImageOpenIso g V
  let yb := (smallEtaleSectionRingEquiv B Y.obj Y.property
    ((opensToBoundedEtale B Y.obj Y.property).obj V)).symm b
  have hgY := (isPullback_basicOpenUnitsHom B Y.obj Y.property hDV b hD).map Φ
  have hX := isPullback_basicOpenUnitsHom B X.obj X.property hD'W (openRingHom g V b) hD'
  have hspec := smallEtaleSectionRingEquiv_symm_openRingHom g V b
  -- the commutativity of the outer rectangle, in the two forms needed
  have wY : Φ.map (basicOpenUnitsHom B Y.obj Y.property hDV b hD) ≫ Φ.map
      (RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) =
      Φ.map (openSheafMap B Y.obj Y.property hDV) ≫ Φ.map yb :=
    (Φ.map_comp _ _).symm.trans ((congrArg Φ.map
      (basicOpenUnitsHom_comp_unitsι B Y.obj Y.property hDV b hD)).trans (Φ.map_comp _ _))
  refine le_antisymm ?_ ?_
  · -- `g⁻¹h_{D(b)} ⟶ h_{D'}`
    rw [← nonempty_hom_openSheaf_iff_le B X.obj X.property]
    have lhs : (Φ.map (basicOpenUnitsHom B Y.obj Y.property hDV b hD) ≫ t) ≫
        RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)) =
        (Φ.map (openSheafMap B Y.obj Y.property hDV) ≫ Φ.map yb) ≫ g.fSharpSet :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hLR.w).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.fSharpSet) wY)))
    have rhs : (Φ.map (openSheafMap B Y.obj Y.property hDV) ≫ e.hom) ≫
        (smallEtaleSectionRingEquiv B X.obj X.property
          ((opensToBoundedEtale B X.obj X.property).obj (inverseImageOpen B X Y g V))).symm
            (openRingHom g V b) =
        (Φ.map (openSheafMap B Y.obj Y.property hDV) ≫ Φ.map yb) ≫ g.fSharpSet := by
      rw [hspec]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (e.hom_inv_id_assoc _)).trans
        (Category.assoc _ _ _).symm)
    exact ⟨(inverseImageOpenIso g D).inv ≫ hX.lift
      (Φ.map (basicOpenUnitsHom B Y.obj Y.property hDV b hD) ≫ t)
      (Φ.map (openSheafMap B Y.obj Y.property hDV) ≫ e.hom) (lhs.trans rhs.symm)⟩
  · -- `h_{D'} ⟶ g⁻¹h_{D(b)}`
    rw [← nonempty_hom_openSheaf_iff_le B X.obj X.property]
    have w₁ : basicOpenUnitsHom B X.obj X.property hD'W (openRingHom g V b) hD' ≫
        RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)) =
        (openSheafMap B X.obj X.property hD'W ≫ e.inv ≫ Φ.map yb) ≫ g.fSharpSet := by
      refine (basicOpenUnitsHom_comp_unitsι B X.obj X.property hD'W (openRingHom g V b)
        hD').trans ?_
      rw [hspec]
      exact (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
    let l := hLR.lift (basicOpenUnitsHom B X.obj X.property hD'W (openRingHom g V b) hD')
      (openSheafMap B X.obj X.property hD'W ≫ e.inv ≫ Φ.map yb) w₁
    have w₂ : l ≫ Φ.map
        (RingedTopos.unitsι (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) =
        (openSheafMap B X.obj X.property hD'W ≫ e.inv) ≫ Φ.map yb :=
      (hLR.lift_snd _ _ w₁).trans (Category.assoc _ _ _).symm
    exact ⟨hgY.lift l (openSheafMap B X.obj X.property hD'W ≫ e.inv) w₂ ≫
      (inverseImageOpenIso g D).hom⟩

/-- The image of an open of an open subscheme lies in that open subscheme. -/
theorem Scheme.Opens.ι_image_le' {T : Scheme.{u}} (V : T.Opens) (U : V.toScheme.Opens) :
    V.ι ''ᵁ U ≤ V := by
  rintro _ ⟨z, _, rfl⟩
  rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact Set.mem_range_self z

/-- **The glued morphism pulls an affine open `V` back to `W_V`.** -/
theorem preimage_glueHom_eq (hg : g.IsLocallyRinged) (V : Y.obj.affineOpens) :
    (B.inclusion.map (glueHom g)) ⁻¹ᵁ (V : Y.obj.Opens) = inverseImageOpen B X Y g V := by
  refine le_antisymm ?_ (inverseImageOpen_le_preimage g V)
  intro x hx
  have hcov := iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf B X Y g
    (fun V'' : Y.obj.affineOpens => (V'' : Y.obj.Opens)) (iSup_affineOpens_eq_top Y.obj)
    (fun V'' => inverseImageOpen B X Y g V'') (fun V'' => nonempty_iso_inverseImageOpen B X Y g V'')
  have hxtop : x ∈ (⊤ : X.obj.Opens) := trivial
  rw [← hcov] at hxtop
  obtain ⟨V'', hxV''⟩ := TopologicalSpace.Opens.mem_iSup.1 hxtop
  obtain ⟨y, rfl⟩ : x ∈ Set.range (inverseImageOpen B X Y g V'').ι := by
    rwa [Scheme.Opens.range_ι]
  have hfy : B.inclusion.map (glueHom g) ((inverseImageOpen B X Y g V'').ι y) =
      (V'' : Y.obj.Opens).ι (openSchemeHom g V'' y) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m y) (glueHom_spec g V'')
  have hmem : openSchemeHom g V'' y ∈ (V'' : Y.obj.Opens).ι ⁻¹ᵁ (V : Y.obj.Opens) := by
    change (V'' : Y.obj.Opens).ι (openSchemeHom g V'' y) ∈ (V : Y.obj.Opens)
    rwa [← hfy]
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hyb, hbV⟩ :=
    (isBasis_basicOpen (V'' : Y.obj.Opens).toScheme).exists_subset_of_mem_open
      hmem ((V'' : Y.obj.Opens).ι ⁻¹ᵁ (V : Y.obj.Opens)).isOpen
  let Db := (V'' : Y.obj.Opens).ι ''ᵁ ((V'' : Y.obj.Opens).toScheme.basicOpen b)
  let W'' := inverseImageOpen B X Y g V''
  let D' := W''.ι ''ᵁ (W''.toScheme.basicOpen (openRingHom g V'' b))
  have hDb : inverseImageOpen B X Y g Db = D' :=
    inverseImageOpen_eq_of_basicOpen g hg (Scheme.Opens.ι_image_le' _ _) b
      ((V'' : Y.obj.Opens).ι.preimage_image_eq _) (Scheme.Opens.ι_image_le' _ _)
      (W''.ι.preimage_image_eq _)
  have hDbV : Db ≤ V := ((V'' : Y.obj.Opens).ι.image_mono hbV).trans
    ((V'' : Y.obj.Opens).ι.image_preimage_le _)
  refine inverseImageOpen_mono g hDbV ?_
  rw [hDb]
  change W''.ι y ∈ W''.ι ''ᵁ _
  rw [Scheme.Hom.apply_mem_image_iff]
  have hy : y ∈ (openSchemeHom g V'') ⁻¹ᵁ ((V'' : Y.obj.Opens).toScheme.basicOpen b) := hyb
  rwa [Scheme.preimage_basicOpen_top, openSchemeHom_appTop] at hy

end Transport

end AlgebraicGeometry

end
