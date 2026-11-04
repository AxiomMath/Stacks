module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportOpen
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.SupportTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset

/-!
# Compact support and extension by zero under a compactification

Let `k` be a field, let `X̄` be proper over `k` and let `j : X ⟶ X̄` be an open immersion in a big
étale site. For an abelian sheaf `F` on the small étale site of `X`, the compactly supported
global sections of `F` are canonically the compactly supported global sections of its extension
by zero `j_! F` on `X̄` — and by Stacks 0F73 the latter are all the global sections of `j_! F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_extensionByZero` — the canonical
  additive equivalence on compactly supported sections.

## Main results

* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_extensionByZero_restrict` — the
  equivalence is characterised by restriction to the open subscheme: the extended section
  restricts to the original one, read through the extension-by-zero adjunction unit.

## Implementation notes

Global sections are the sections over the final object of the small étale site, and
`AlgebraicGeometry.SmallEtale.baseChangeFinalIso` identifies the final object of the small étale
site of `X` with the base change along `j` of the final object of the small étale site of `X̄`.
Injectivity of the canonical map is immediate from Stacks 0F74; surjectivity is where the
properness of `X̄` is used. Given a global section of `j_! F`, the identification of `j_! F` with
the proper-support subsheaf of `j_* F` produces a section of `F` whose support is proper over the
base change of the final object; transporting that properness along
`AlgebraicGeometry.isProperOver_preimage_of_iso` makes it properness over `k`, which is exactly
compact support. The resulting compactly supported section has the given section as its image,
because the canonical map from extension by zero to direct image is a monomorphism and the two
agree after restriction along the graph.

## References

* [Stacks Project, Tag 0F75](https://stacks.math.columbia.edu/tag/0F75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-! ### Base change of the final object -/

section FinalObject

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The inverse of `AlgebraicGeometry.SmallEtale.baseChangeFinalIso`, followed by the projection
of the fibre product to the ambient scheme, is `f`. -/
public theorem baseChangeFinalIso_inv_comp_fst :
    haveI := hasPullbacks_bigEtaleSite B
    (SmallEtale.toScheme B X.obj X.property).map (baseChangeFinalIso B f).inv ≫
        B.inclusion.map
          (pullback.fst (SmallEtale.final B Y.obj Y.property).obj.hom f) =
      B.inclusion.map f := by
  have := hasPullbacks_bigEtaleSite B
  have hsnd : ((baseChangeFinalIso B f).inv).hom.left ≫
      pullback.snd (SmallEtale.final B Y.obj Y.property).obj.hom f = 𝟙 _ :=
    (asIso (pullback.snd (𝟙 (B.obj Y.obj Y.property)) f)).inv_hom_id
  have hfst : pullback.fst (SmallEtale.final B Y.obj Y.property).obj.hom f =
      pullback.snd (SmallEtale.final B Y.obj Y.property).obj.hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  have hb : ((baseChangeFinalIso B f).inv).hom.left ≫
      pullback.fst (SmallEtale.final B Y.obj Y.property).obj.hom f = f :=
    (congrArg (fun t => ((baseChangeFinalIso B f).inv).hom.left ≫ t) hfst).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ f) hsnd)).trans (Category.id_comp f))
  exact congrArg B.inclusion.map hb

end FinalObject

/-! ### Transport of compact support along an isomorphism of sheaves -/

section Transport

variable (k : Type u) [Field k] (B : BigEtaleSite.{u}) (X : B.Scheme)
  (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}

/-- An isomorphism of abelian sheaves preserves compact support, so it restricts to an additive
equivalence of the subgroups of compactly supported global sections. -/
public noncomputable def compactlySupportedSectionsMapIso (e : F ≅ G) :
    compactlySupportedSections k X.obj f B X.property F ≃+
      compactlySupportedSections k X.obj f B X.property G := by
  refine
    { toFun := fun s =>
        ⟨e.hom.hom.app (op (SmallEtale.final B X.obj X.property)) s.1, ?_⟩
      invFun := fun s =>
        ⟨e.inv.hom.app (op (SmallEtale.final B X.obj X.property)) s.1, ?_⟩
      left_inv := fun s => Subtype.ext <| Iso.hom_inv_id_apply
        (((sheafToPresheaf (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.{v}).mapIso e).app (op (SmallEtale.final B X.obj X.property))) s.1
      right_inv := fun s => Subtype.ext <| Iso.inv_hom_id_apply
        (((sheafToPresheaf (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.{v}).mapIso e).app (op (SmallEtale.final B X.obj X.property))) s.1
      map_add' := fun s t => Subtype.ext <|
        (e.hom.hom.app (op (SmallEtale.final B X.obj X.property))).hom.map_add s.1 t.1 }
  · rw [mem_compactlySupportedSections,
      zeroOpen_sheafIso B X.obj X.property e (SmallEtale.final B X.obj X.property) s.1]
    exact s.2
  · have h : zeroOpen B X.obj X.property F (SmallEtale.final B X.obj X.property)
          (e.inv.hom.app (op (SmallEtale.final B X.obj X.property)) s.1) =
        zeroOpen B X.obj X.property G (SmallEtale.final B X.obj X.property) s.1 :=
      zeroOpen_sheafIso B X.obj X.property e.symm (SmallEtale.final B X.obj X.property) s.1
    rw [mem_compactlySupportedSections, h]
    exact s.2

end Transport

/-! ### Restriction of an extended global section along the graph -/

section GraphRestriction

variable (B : BigEtaleSite.{u}) {X : B.Scheme} (U : SmallEtale B X.obj X.property)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) AddCommGrpCat.{u + 1})

/-- Along an open immersion the extension-by-zero unit, composed with the identification of the
two descriptions of restriction, is an isomorphism from `F` to the restriction of `j_! F`. -/
public noncomputable def extensionByZeroRestrictionIso :
    F ≅ (openRestriction.{u, u} B U.obj.hom).obj
        ((abelianExtensionByZero B X.obj X.property U).obj F) :=
  haveI : IsIso ((abelianExtensionByZeroAdjunction B X.obj X.property U).unit.app F) :=
    abelianExtensionByZeroAdjunction_unit_isIso B X.obj X.property U F
  asIso ((abelianExtensionByZeroAdjunction B X.obj X.property U).unit.app F) ≪≫
    (openRestrictionIso.{u, u} B U.obj.hom).app
      ((abelianExtensionByZero B X.obj X.property U).obj F)

private theorem extensionByZeroRestrictionIso_hom_app
    (W : SmallEtale B U.obj.left.obj U.obj.left.property) (s : F.obj.obj (op W)) :
    (extensionByZeroRestrictionIso B U F).hom.hom.app (op W) s =
      ((openRestrictionIso.{u, u} B U.obj.hom).hom.app
          ((abelianExtensionByZero B X.obj X.property U).obj F)).hom.app (op W)
        (((abelianExtensionByZeroAdjunction B X.obj X.property U).unit.app F).hom.app
          (op W) s) := rfl

/-- The canonical map from extension by zero to the direct image, read on global sections and
restricted along the graph of the final object, inverts the extension-by-zero unit. -/
private theorem abelianExtensionByZeroToPushforward_final_restrict
    (s : ((abelianExtensionByZero B X.obj X.property U).obj F).obj.obj
      (op (SmallEtale.final B X.obj X.property))) :
    ((abelianExtensionByZeroAdjunction B X.obj X.property U).unit.app F).hom.app
        (op (SmallEtale.final B U.obj.left.obj U.obj.left.property))
        (F.obj.map (baseChangeFinalIso B U.obj.hom).inv.op
          (((abelianExtensionByZeroToPushforward B X.obj X.property U).app F).hom.app
            (op (SmallEtale.final B X.obj X.property)) s)) =
      ((abelianExtensionByZero B X.obj X.property U).obj F).obj.map
        ((SmallEtale.finalIsTerminal B X.obj X.property).from
          ((smallEtalePostcompose B X.obj X.property U).obj
            (SmallEtale.final B U.obj.left.obj U.obj.left.property))).op s := by
  let base := smallEtaleBaseChange B U.obj.hom
  let qIso := baseChangeFinalIso B U.obj.hom
  let ext := abelianExtensionByZero B X.obj X.property U
  let unit := (abelianExtensionByZeroAdjunction B X.obj X.property U).unit.app F
  let gamma := abelianExtensionByZeroToPushforward B X.obj X.property U
  let W := SmallEtale.final B U.obj.left.obj U.obj.left.property
  let Xf := SmallEtale.final B X.obj X.property
  let post := smallEtalePostcompose B X.obj X.property U
  let V := post.obj W
  let w := (SmallEtale.finalIsTerminal B X.obj X.property).from V
  let graph := smallEtaleGraph B X.obj X.property U W
  have : IsIso unit := abelianExtensionByZeroAdjunction_unit_isIso B X.obj X.property U F
  have hcomp : graph ≫ base.map w = qIso.inv :=
    (IsTerminal.ofIso (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property)
      qIso.symm).hom_ext _ _
  have hnatural : (gamma.app F).hom.app (op V) ((ext.obj F).obj.map w.op s) =
      F.obj.map (base.map w).op ((gamma.app F).hom.app (op Xf) s) :=
    ConcreteCategory.congr_hom ((gamma.app F).hom.naturality w.op) s
  have hnat : F.obj.map graph.op
      ((gamma.app F).hom.app (op V) ((ext.obj F).obj.map w.op s)) =
      F.obj.map qIso.inv.op ((gamma.app F).hom.app (op Xf) s) := by
    have hcompose : (F.obj.map (base.map w).op ≫ F.obj.map graph.op)
        ((gamma.app F).hom.app (op Xf) s) =
        F.obj.map qIso.inv.op ((gamma.app F).hom.app (op Xf) s) := by
      rw [← F.obj.map_comp, ← op_comp, hcomp]
    rw [hnatural]
    exact hcompose
  let z := (inv (unit.hom.app (op W))) ((ext.obj F).obj.map w.op s)
  have hz : unit.hom.app (op W) z = (ext.obj F).obj.map w.op s :=
    Iso.inv_hom_id_apply (asIso (unit.hom.app (op W))) _
  have hgraph : F.obj.map graph.op
      ((gamma.app F).hom.app (op V) (unit.hom.app (op W) z)) = z :=
    abelianExtensionByZeroToPushforward_graph B X.obj X.property U F W z
  have hzq : z = F.obj.map qIso.inv.op ((gamma.app F).hom.app (op Xf) s) := by
    rwa [← hz, hgraph] at hnat
  rwa [← hzq]

end GraphRestriction

/-! ### Compact support under a compactification -/

section Compactification

variable (k : Type u) [Field k] (B : BigEtaleSite.{u}) (Xbar : B.Scheme)
  (fbar : Xbar.obj ⟶ Spec (.of k)) [IsProper fbar]
  (U : SmallEtale B Xbar.obj Xbar.property) [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) AddCommGrpCat.{u + 1})

/-- Extension by zero on compactly supported global sections: transport along the identification
of `F` with the restriction of `j_! F`, followed by the canonical injection of Stacks 0F74. -/
public noncomputable def extensionByZeroCompactSupportMap :
    compactlySupportedSections k U.obj.left.obj (B.inclusion.map U.obj.hom ≫ fbar) B
        U.obj.left.property F →+
      compactlySupportedSections k Xbar.obj fbar B Xbar.property
        ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F) where
  toFun s :=
    (compactlySupportedSections_openInclusion k B U.obj.hom fbar
        ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F)).val
      (compactlySupportedSectionsMapIso k B U.obj.left (B.inclusion.map U.obj.hom ≫ fbar)
        (extensionByZeroRestrictionIso B U F) s)
  map_zero' := by simp
  map_add' s t := by simp

/-- The extended section restricts, over the open subscheme, to the original section read
through the extension-by-zero adjunction unit. This is the characterising property of the
canonical map on compactly supported sections. -/
private theorem extensionByZeroCompactSupportMap_restrict
    (s : compactlySupportedSections k U.obj.left.obj (B.inclusion.map U.obj.hom ≫ fbar) B
      U.obj.left.property F) :
    ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F).obj.map
        ((SmallEtale.finalIsTerminal B Xbar.obj Xbar.property).from
          ((smallEtalePostcompose B Xbar.obj Xbar.property U).obj
            (SmallEtale.final B U.obj.left.obj U.obj.left.property))).op
        (extensionByZeroCompactSupportMap k B Xbar fbar U F s).1 =
      ((abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F).hom.app
        (op (SmallEtale.final B U.obj.left.obj U.obj.left.property)) s.1 := by
  let j := U.obj.hom
  let ext := abelianExtensionByZero B Xbar.obj Xbar.property U
  let base := smallEtaleBaseChange B j
  let post := smallEtalePostcompose B Xbar.obj Xbar.property U
  let unit := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
  let WU := SmallEtale.final B U.obj.left.obj U.obj.left.property
  let Xf := SmallEtale.final B Xbar.obj Xbar.property
  let V := post.obj WU
  let w := (SmallEtale.finalIsTerminal B Xbar.obj Xbar.property).from V
  let graph := smallEtaleGraph B Xbar.obj Xbar.property U WU
  let qIso := baseChangeFinalIso B j
  let F' := (openRestriction.{u, u} B j).obj (ext.obj F)
  let unitBase := (base.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).unit.app (ext.obj F)
  let openIso := (openRestrictionIso.{u, u} B j).hom.app (ext.obj F)
  let i := compactlySupportedSectionsMapIso k B U.obj.left (B.inclusion.map j ≫ fbar)
    (extensionByZeroRestrictionIso B U F)
  let phi := compactlySupportedSections_openInclusion k B j fbar (ext.obj F)
  let out := (extensionByZeroCompactSupportMap k B Xbar fbar U F s).1
  let r : base.obj Xf ⟶ WU :=
    (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property).from (base.obj Xf)
  have hr : r = qIso.hom :=
    (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property).hom_ext _ _
  have hcomp' : (r ≫ graph) ≫ base.map w = 𝟙 (base.obj Xf) :=
    (IsTerminal.ofIso (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property)
      qIso.symm).hom_ext _ _
  have hNat : unitBase.hom.app (op V) ((ext.obj F).obj.map w.op out) =
      F'.obj.map (base.map w).op (unitBase.hom.app (op Xf) out) :=
    ConcreteCategory.congr_hom (unitBase.hom.naturality w.op) out
  have hi : (i s).1 = openIso.hom.app (op WU) (unit.hom.app (op WU) s.1) :=
    extensionByZeroRestrictionIso_hom_app B U F WU s.1
  have hphi : F'.obj.map r.op ((i s).1) = unitBase.hom.app (op Xf) out :=
    (phi.property.2 (i s)).1
  rw [hi] at hphi
  have hopenOut : openIso.hom.app (op WU) ((ext.obj F).obj.map w.op out) =
      F'.obj.map graph.op (unitBase.hom.app (op V) ((ext.obj F).obj.map w.op out)) :=
    openRestrictionIso_app_apply.{u, u} B U (ext.obj F) WU ((ext.obj F).obj.map w.op out)
  have hmaps : F'.obj.map (base.map w).op ≫ F'.obj.map graph.op ≫ F'.obj.map r.op = 𝟙 _ := by
    rw [← F'.obj.map_comp, ← F'.obj.map_comp, ← op_comp, ← op_comp, hcomp', op_id,
      F'.obj.map_id]
  have hright : F'.obj.map r.op (openIso.hom.app (op WU) ((ext.obj F).obj.map w.op out)) =
      unitBase.hom.app (op Xf) out := by
    rw [hopenOut, hNat]
    exact ConcreteCategory.congr_hom hmaps (unitBase.hom.app (op Xf) out)
  have : IsIso r := hr ▸ (inferInstance : IsIso qIso.hom)
  exact (ConcreteCategory.bijective_of_isIso (openIso.hom.app (op WU))).1
    ((ConcreteCategory.bijective_of_isIso (F'.obj.map r.op)).1 (hright.trans hphi.symm))

/-- The canonical map on compactly supported sections is injective: both of its factors are. -/
public theorem extensionByZeroCompactSupportMap_injective :
    Function.Injective (extensionByZeroCompactSupportMap k B Xbar fbar U F) := fun _ _ h =>
  (compactlySupportedSectionsMapIso k B U.obj.left (B.inclusion.map U.obj.hom ≫ fbar)
      (extensionByZeroRestrictionIso B U F)).injective
    ((compactlySupportedSections_openInclusion k B U.obj.hom fbar
      ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F)).property.1 h)

/-- The canonical map on compactly supported sections is surjective. This is where properness of
the compactification enters: a global section of `j_! F` corresponds to a section of `F` over the
base change of the final object whose support is proper over that base change, and transporting
that properness along the identification of the base change with the final object makes it
properness over the base field. -/
public theorem extensionByZeroCompactSupportMap_surjective :
    Function.Surjective (extensionByZeroCompactSupportMap k B Xbar fbar U F) := by
  classical
  let j := U.obj.hom
  let ext := abelianExtensionByZero B Xbar.obj Xbar.property U
  let base := smallEtaleBaseChange B j
  let unit := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
  let WU := SmallEtale.final B U.obj.left.obj U.obj.left.property
  let Xf := SmallEtale.final B Xbar.obj Xbar.property
  let Gsrc := (fShriekSubsheaf B j F).val
  let extToPush := abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U
  let extToPushW := (extToPush.app F).hom.app (op Xf)
  let qIso := baseChangeFinalIso B j
  let schemeIso := (SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).mapIso qIso
  have hfbarProper : IsProper fbar := inferInstance
  have hfbarLFT : LocallyOfFiniteType fbar := inferInstance
  intro t
  obtain ⟨a, ha⟩ : extToPushW t.1 ∈ Set.range (Gsrc.arrow.hom.app (op Xf)) :=
    (abelianExtensionByZeroToPushforward_range_eq_fShriekSubsheaf
      B Xbar.obj Xbar.property U F Xf).subset (Set.mem_range_self t.1)
  let b := Gsrc.arrow.hom.app (op Xf) a
  have hbproper : properSupportSections B j F Xf b :=
    ((fShriekSubsheaf B j F).property Xf b).mp ⟨a, rfl⟩
  let Q := base.obj Xf
  let Zb : Closeds ((SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).obj Q) :=
    (zeroOpen B U.obj.left.obj U.obj.left.property F Q b).compl
  let pQ := B.inclusion.map (pullback.fst Xf.obj.hom j)
  have hpQ : LocallyOfFiniteType pQ := locallyOfFiniteType_baseChangeProjection B j Xf
  have hbp : IsProper ((Scheme.IdealSheafData.vanishingIdeal Zb).subschemeι ≫ pQ) := hbproper
  have hpQf : LocallyOfFiniteType (pQ ≫ fbar) :=
    MorphismProperty.comp_mem (W := @LocallyOfFiniteType) pQ fbar hpQ hfbarLFT
  have hIproper :
      IsProper ((Scheme.IdealSheafData.vanishingIdeal Zb).subschemeι ≫ pQ ≫ fbar) :=
    Category.assoc (Scheme.IdealSheafData.vanishingIdeal Zb).subschemeι pQ fbar ▸
      MorphismProperty.comp_mem (W := @IsProper)
        ((Scheme.IdealSheafData.vanishingIdeal Zb).subschemeι ≫ pQ) fbar hbp hfbarProper
  have hproj : schemeIso.inv ≫ pQ = B.inclusion.map j := baseChangeFinalIso_inv_comp_fst B j
  let sigma := F.obj.map qIso.inv.op b
  have hZ : Zb.preimage schemeIso.symm.hom.continuous =
      (zeroOpen B U.obj.left.obj U.obj.left.property F WU sigma).compl :=
    Closeds.ext (supportSection_map B U.obj.left.obj U.obj.left.property F Q WU qIso.inv b).symm
  have hsigmacompact : sigma ∈ compactlySupportedSections k U.obj.left.obj
      (B.inclusion.map j ≫ fbar) B U.obj.left.property F := by
    rw [mem_compactlySupportedSections, ← hZ]
    exact @isProperOver_preimage_of_iso _ _ _ schemeIso.symm (pQ ≫ fbar)
      (B.inclusion.map j ≫ fbar)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ fbar) hproj)) hpQf Zb hIproper
  refine ⟨⟨sigma, hsigmacompact⟩, Subtype.ext ?_⟩
  let out := (extensionByZeroCompactSupportMap k B Xbar fbar U F ⟨sigma, hsigmacompact⟩).1
  let post := smallEtalePostcompose B Xbar.obj Xbar.property U
  let w := (SmallEtale.finalIsTerminal B Xbar.obj Xbar.property).from (post.obj WU)
  have hrestr : (ext.obj F).obj.map w.op out = unit.hom.app (op WU) sigma :=
    extensionByZeroCompactSupportMap_restrict k B Xbar fbar U F ⟨sigma, hsigmacompact⟩
  have houtBridge : unit.hom.app (op WU) (F.obj.map qIso.inv.op (extToPushW out)) =
      (ext.obj F).obj.map w.op out :=
    abelianExtensionByZeroToPushforward_final_restrict B U F out
  have : IsIso unit :=
    abelianExtensionByZeroAdjunction_unit_isIso B Xbar.obj Xbar.property U F
  have hqOut : F.obj.map qIso.inv.op (extToPushW out) = sigma :=
    (ConcreteCategory.bijective_of_isIso (unit.hom.app (op WU))).1 (houtBridge.trans hrestr)
  have hqT : F.obj.map qIso.inv.op (extToPushW t.1) = sigma := by rw [← ha]
  have hpushout : extToPushW out = extToPushW t.1 :=
    (ConcreteCategory.bijective_of_isIso (F.obj.map qIso.inv.op)).1 (hqOut.trans hqT.symm)
  have : Mono (extToPush.app F) :=
    abelianExtensionByZeroToPushforward_mono B Xbar.obj Xbar.property U F
  exact (AddCommGrpCat.mono_iff_injective _).mp (inferInstance : Mono extToPushW) hpushout

/-- **Stacks 0F75.** For an open immersion `j : X ⟶ X̄` with `X̄` proper over a field `k`, the
compactly supported global sections of an abelian sheaf `F` on the small étale site of `X` are
canonically the compactly supported global sections of its extension by zero `j_! F` on `X̄`. -/
@[stacks 0F75 "canonical isomorphism"]
public noncomputable def compactlySupportedSections_extensionByZero :
    compactlySupportedSections k U.obj.left.obj (B.inclusion.map U.obj.hom ≫ fbar) B
        U.obj.left.property F ≃+
      compactlySupportedSections k Xbar.obj fbar B Xbar.property
        ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F) :=
  AddEquiv.ofBijective (extensionByZeroCompactSupportMap k B Xbar fbar U F)
    ⟨extensionByZeroCompactSupportMap_injective k B Xbar fbar U F,
      extensionByZeroCompactSupportMap_surjective k B Xbar fbar U F⟩

/-- **Stacks 0F75.** The canonical equivalence is determined by the fact that restriction of the
extended section to the open subscheme is the original section, identified through the
extension-by-zero adjunction unit. -/
@[stacks 0F75 "restriction characterization"]
public theorem compactlySupportedSections_extensionByZero_restrict
    (s : compactlySupportedSections k U.obj.left.obj (B.inclusion.map U.obj.hom ≫ fbar) B
      U.obj.left.property F) :
    ((abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F).hom.app
        (op (SmallEtale.final B U.obj.left.obj U.obj.left.property)) s.1 =
      ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F).obj.map
        ((SmallEtale.finalIsTerminal B Xbar.obj Xbar.property).from U).op
        (compactlySupportedSections_extensionByZero k B Xbar fbar U F s).1 :=
  (extensionByZeroCompactSupportMap_restrict k B Xbar fbar U F s).symm

end Compactification

end AlgebraicGeometry.SmallEtale

end
